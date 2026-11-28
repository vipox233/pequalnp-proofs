import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_40752

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
  Nat.testBit (4276808384 * 2 ^ 32 + 4272603264) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0002a36f0884ae1c#64 ++ 0x0000546de11095c3#64 ++ 0xa047e7ff088ffe3b#64 ++ 0xf408fcffe111ffc7#64 : BitVec 256),
   (0x419988e170b262e8#64 ++ 0x0833311c2e164c5d#64 ++ 0xc3b998e3f0f267fe#64 ++ 0xf877331c7e1e4cff#64 : BitVec 256),
   (0x2c2e1702bb038570#64 ++ 0x0585c2e0576070ae#64 ++ 0xfc3e1f03ff0387ff#64 ++ 0x7f87c3e07fe070ff#64 : BitVec 256),
   (0x16c01db40ddc0780#64 ++ 0x22d803b681bb80f0#64 ++ 0x7fc01ffc1ffc07c7#64 ++ 0xeff803ff83ff80f8#64 : BitVec 256),
   (0x9b7d4000166b5000#64 ++ 0x936fa80002cd6a00#64 ++ 0xffffe0001ffff807#64 ++ 0xbffffc0003ffff00#64 : BitVec 256),
   (0x9ff7fedbc0000000#64 ++ 0x53feffdb78000000#64 ++ 0x9fffffffe0000007#64 ++ 0xd3fffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 3]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [7, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [8, 5]⟩, ⟨.and, [10, 3]⟩, ⟨.or, [0, 12]⟩, ⟨.and, [13, 9]⟩, ⟨.or, [11, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0002a36f0884ae1c 0x0000546de11095c3 0xa047e7ff088ffe3b 0xf408fcffe111ffc7

def z1 : W := mkw 0x16c01db40ddc0780 0x22d803b681bb80f0 0x7fc01ffc1ffc07c7 0xeff803ff83ff80f8

def z2 : W := mkw 0x2c2e1702bb038570 0x0585c2e0576070ae 0xfc3e1f03ff0387ff 0x7f87c3e07fe070ff

def z3 : W := mkw 0x419988e170b262e8 0x0833311c2e164c5d 0xc3b998e3f0f267fe 0xf877331c7e1e4cff

def z4 : W := mkw 0x9b7d4000166b5000 0x936fa80002cd6a00 0xffffe0001ffff807 0xbffffc0003ffff00

def z5 : W := mkw 0x9ff7fedbc0000000 0x53feffdb78000000 0x9fffffffe0000007 0xd3fffffffc000000

def z6 : W := mkw 0xbf7d5400b76b5160 0x97efaa8016ed6a2c 0xfffff800fffff9c7 0xbfffff001fffff38

def z7 : W := mkw 0x16c01cb005d80380 0x22d8039600bb0070 0x5f8018e017f007c6 0xebf0031c02fe00f8

def z8 : W := mkw 0x9f77f65bc0000000 0x53eefecb78000000 0x9c7fe71fe0000001 0x138ffce3fc000000

def z9 : W := mkw 0x0002a24b0000a81c 0x0000544960001503 0x8047e7ff0003f83b 0xd008fcffe0007f07

def z10 : W := mkw 0x04801db409940780 0x209003b6813280f0 0x43801ffc10f007c6 0xe87003ff821e00f8

def z11 : W := mkw 0x04801db40ddc0780 0x209003b681bb80f0 0x60001ffc1ffc07c0 0x6c0003ff83ff80f8

def z12 : W := mkw 0x0000000000000000 0x0000000000000000 0xa006000008038003 0x3400c00001007000

def z13 : W := mkw 0x9ff7fedbc0000000 0x53feffdb78000000 0xbfffffffe88ff807 0xf7fffffffd11ff00

def z14 : W := mkw 0x4008806130b262e8 0x0801100c26164c5d 0xc00180e310f267fa 0xf800301c621e4cff

def z15 : W := mkw 0x0400140000000000 0x0080028000000000 0x1c001f0000000007 0x438003e000000000

def z16 : W := mkw 0x9351400004685000 0x926a2800008d0a00 0x03c1e00000fc7800 0x80783c00001f8f00

def z17 : W := mkw 0x9ff7fedbc4685000 0xd3feffdb788d0a00 0x9fffffffe0fc7807 0xd3fffffffc1f8f00

def z18 : W := mkw 0x419188e140b06288 0x0832311c28160c51 0x83b998e3e0f06006 0xd077331c7c1e0c00

def z19 : W := mkw 0x4008002030b262e8 0x0801000406164c5d 0x4000000010f267f8 0x28000000021e4cff

def z20 : W := mkw 0x9ffffedbd66b5000 0xd3ffffdb7acd6a00 0xfffffffffffff807 0xffffffffffffff00

def z21 : W := mkw 0x0002a36f0884ae1c 0x0000546de11095c3 0x000007ff00000638 0x400000ffe00000c7

def z22 : W := mkw 0x1240000004480000 0x0248000000890000 0x7fc000001ffc0007 0xaff8000003ff8000

def z23 : W := mkw 0x2c2eb74bbb038570 0x0585d6e9776070ae 0xfc7fffffff0387ff 0xff8fffffffe070ff

def z24 : W := mkw 0x0000002404dc0280 0x20000004809b8050 0x0000000000fc0000 0x00000000001f8000

def z25 : W := mkw 0x04801db409940780 0x209003b6813280f0 0x00001ffc000007c0 0x400003ff800000f8

def z26 : W := mkw 0x9ffd5db41fff5780 0xb3ffabb683ffeaf0 0xfffffffc1fffffc7 0xffffffff83fffff8

def z27 : W := mkw 0x9ff7fedbc0000000 0x53feffdb78000000 0x1fc7e7fc00000001 0x83f8fcff80000000

def z28 : W := mkw 0x4191088040304080 0x0832211008060810 0x0380000000700000 0x00700000000e0000

def z29 : W := mkw 0x4008012438b6eefc 0x080100248716dddf 0x6000000018fffff8 0x2c000000031fffff

def z30 : W := mkw 0x019188e140802208 0x0032311c28100441 0x83b998e3e082663e 0xf077331c7c104cc7

def z31 : W := mkw 0x0008000030020060 0x000100000600400c 0xc0381803f00207fe 0x780703007e0040ff

def z32 : W := mkw 0x6dbf9fe3fbb3e7f8 0x0db7f3fc7f767cff 0xffbf9fe3fff3e7ff 0xfff7f3fc7ffe7cff

def z33 : W := mkw 0xbf7f5702bf6bd570 0x97efeae057ed7aae 0xffffff03ffffffff 0xffffffe07fffffff

def z34 : W := mkw 0xdbfdc8e176fb72e8 0x9b7fb91c2edf6e5d 0xfffff8e3ffffffff 0xffffff1c7fffffff

def z35 : W := mkw 0x4199a8ed70b66aec 0x0833351dae16cd5d 0xc3f9f8fff0fe7ffe 0xf87f3f1ffe1fcfff

def z36 : W := mkw 0x000001240ddc0780 0x2000002481bb80f0 0x600000001ffc07c0 0x2c00000003ff80f8

def z37 : W := mkw 0x9ff7ffffc884ae1c 0x53fefffff91095c3 0xbfffffffe88ffe3f 0xf7fffffffd11ffc7

def z38 : W := mkw 0x000001240884ae1c 0x00000024811095c3 0x20000000088ffe38 0x240000000111ffc7

def z39 : W := mkw 0x9ff55c90c0000000 0x53feab9218000000 0x1fb81800e0000004 0x03f703001c000000

def z40 : W := mkw 0x282e0202b2038070 0x0505c0405640700e 0x803e0003e0038038 0x1007c0007c007007

def z41 : W := mkw 0x69bf8ae3f2b3e2f8 0x0d37f15c7e567c5f 0xc3bf98e3f0f3e7fe 0xf877f31c7e1e7cff

def z42 : W := mkw 0x9351400000000000 0x126a280000000000 0x03c1e00000000000 0x80783c0000000000

def z43 : W := mkw 0x2c2e1726bb878770 0x0585c2e4d770f0ee 0xfc7e1fffff8f87ff 0xff8fc3fffff1f0ff

def z44 : W := mkw 0x0002a24b0000a81c 0x0000544960001503 0x8007e0030003f838 0x1000fc0060007f07

def z45 : W := mkw 0x9ff55c90c0000000 0x53feab9218000000 0x1ff81ffce0000007 0xc3ff03ff9c000000

def z46 : W := mkw 0x0000000000000000 0x0000000000000000 0xa047e000088ff803 0xb408fc000111ff00

def z47 : W := mkw 0x419988e170b262e8 0x0833311c2e164c5d 0x43b818e3f07007fc 0x4877031c7e0e00ff

def z48 : W := mkw 0x0c26160280000000 0x0184c2c050000000 0x9c3e1f03e0000007 0x5387c3e07c000000

def z49 : W := mkw 0x0000000000000000 0x0000000000000000 0x20466000080d9801 0x0408cc000101b300

def z50 : W := mkw 0x0c2c15001b030500 0x018582a0036060a0 0xfc3e1f001f0387c7 0x7f87c3e003e070f8

def z51 : W := mkw 0x0000000020000060 0x000000000400000c 0x00001803e00007f8 0x400003007c0000ff

def z52 : W := mkw 0x9b7de06d16ef7a0c 0x936fbc0da2ddef41 0xffffe0fc1ffff807 0xbffffc1f83ffff00

def z53 : W := mkw 0x0000a06d00842a0c 0x0000140da0108541 0x0041e0fc008c7800 0x80083c1f80118f00

def z54 : W := mkw 0x2c2c1400b3030160 0x058582801660602c 0x5c381800f70001c4 0x0b8703001ee00038

def z55 : W := mkw 0x1240000004480000 0x0248000000890000 0x03c0000000fc0000 0x80780000001f8000

def z56 : W := mkw 0x0402b76f0984af1c 0x008056ede13095e3 0xfc47ffff1f8fffff 0xff88ffffe3f1ffff

def z57 : W := mkw 0x8935400000000000 0x1126a80000000000 0x803fe00000000000 0x1007fc0000000000

def z58 : W := mkw 0x24021702a9008570 0x048042e0552010ae 0x00001f03e00007f8 0x400003e07c0000ff

def z59 : W := mkw 0x0119000010224000 0x0023200002044800 0xe3ffe00018fff807 0xbc7ffc00031fff00

def z60 : W := mkw 0x9b7d4000166b5000 0x936fa80002cd6a00 0x5fb8000017700004 0x0bf7000002ee0000

def z61 : W := mkw 0x9ff7ffffc8840600 0x53fefffff91080c0 0xbfffffffe88c0607 0xf7fffffffd1180c0

def z62 : W := mkw 0x0008806130822268 0x0001100c2610444d 0xc03998e3f08267fe 0xf807331c7e104cff

def z63 : W := mkw 0x0002a34b0800ac1c 0x0000546961001583 0xa007e7030803fe3b 0x7400fce061007fc7

def z64 : W := mkw 0x0000816508842608 0x0000102ca11084c1 0xa04187ff088e663b 0xf40830ffe111ccc7

def z65 : W := mkw 0x9b75400006491000 0x936ea80000c92200 0xbfffe0000f0d9807 0x97fffc0001e1b300

def z66 : W := mkw 0x4191a8ed40b46a8c 0x0832351da8168d51 0x03c1e0fc00fc7800 0x80783c1f801f8f00

def z67 : W := mkw 0x0193aacb40000000 0x0032755968000000 0x83ffffffe0000007 0xd07ffffffc000000

def z68 : W := mkw 0x0ca6bedbc0000000 0x4194d7db78000000 0x9c3e1fffe0000007 0x5387c3fffc000000

def z69 : W := mkw 0x200801243b87af7c 0x040100248770f5ef 0x600000001f8ffff8 0x2c00000003f1ffff

def z70 : W := mkw 0x2c2eb76fbb87af7c 0x0585d6edf770f5ef 0xfc7fffffff8fffff 0xff8ffffffff1ffff

def z71 : W := mkw 0x000001040d4c0500 0x2000002081a980a0 0x200000000f0c0000 0x0400000001e18000

def z72 : W := mkw 0x0002a24bc0000000 0x4000544978000000 0x00000003e0000000 0x000000007c000000

def z73 : W := mkw 0x200801003f6bd570 0x8401002007ed7aae 0x600000001ffffff8 0x2c00000003ffffff

def z74 : W := mkw 0x0000012408840600 0x00000024811080c0 0xa047e7fc088ffe03 0xf408fcff8111ffc0

def z75 : W := mkw 0xc9bdc8e172b372e8 0x9937b91c2e566e5d 0xc3bff8e3f0f3fffe 0xf877ff1c7e1e7fff

def z76 : W := mkw 0x16c01c9005580180 0x22d8039200ab0030 0x5f801800177001c4 0x0bf0030002ee0038

def z77 : W := mkw 0x8937e24bc0000000 0x5126fc4978000000 0x803fe003e0000000 0x1007fc007c000000

def z78 : W := mkw 0x16c01db40ddc0780 0x22d803b681bb80f0 0xffc7fffc1fffffc7 0xfff8ffff83fffff8

def z79 : W := mkw 0x64829fe3e990a7f8 0x0c9053fc7d3214ff 0x00001fe3e00007f8 0x400003fc7c0000ff

def z80 : W := mkw 0x16c09df50ddc2788 0x22d813bea1bb84f1 0xffc19fff1ffe67ff 0xfff833ffe3ffccff

def z81 : W := mkw 0x3e6e1702bf4b8570 0x07cdc2e057e970ae 0xfffe1f03ffff87ff 0xffffc3e07ffff0ff

def z82 : W := mkw 0xbfffffdbfb038570 0x57fffffb7f6070ae 0xffffffffff0387ff 0xffffffffffe070ff

def z83 : W := mkw 0x93d1489040000000 0x527a291208000000 0x0380000000000000 0x0070000000000000

def z84 : W := mkw 0x0002230e08048c14 0x00004461c1009182 0x2046671c080d9801 0x0408cce38101b300

def z85 : W := mkw 0x419babef78b6eefc 0x0833757def16dddf 0xe3fffffff8ffffff 0xfc7fffffff1fffff

def z86 : W := mkw 0x2c2e1702bb038570 0x0585c2e0576070ae 0xfc7fff03ff8fffff 0xff8fffe07ff1ffff

def z87 : W := mkw 0x0002a24b00000000 0x0000544960000000 0x8047e7ff00000003 0xd008fcffe0000000

def z88 : W := mkw 0x200801003b038570 0x04010020076070ae 0x600000001f0387f8 0x2c00000003e070ff

def z89 : W := mkw 0x17d19cd140000000 0x02fa339a28000000 0x9ff99fffe0000007 0xd3ff33fffc000000

def z90 : W := mkw 0x57d99df57dfe67e8 0x2afb33beafbfccfd 0xfff99ffffffe67ff 0xffff33ffffffccff

def z91 : W := mkw 0xdffffedbf0226068 0x5bffffdb7e044c0d 0x9fffffffe002603f 0xd3fffffffc004c07

def z92 : W := mkw 0x0119000010224000 0x0023200002044800 0xc3b9800010f26006 0xb8773000021e4c00

def z93 : W := mkw 0x9a64400006491000 0x934c880000c92200 0x3c4660000f0d9801 0x0788cc0001e1b300

def z94 : W := mkw 0x082c000032030060 0x010580000640600c 0xfc3e1803ff0387ff 0x7f87c3007fe070ff

def z95 : W := mkw 0x12c009b40cdc0680 0x22580136819b80d0 0x23c007fc08fc0603 0xe47800ff811f80c0

def z96 : W := mkw 0x419988c1703240e0 0x083331182e06481c 0xc3b998e3f07001c6 0xd877331c7e0e0038

def z97 : W := mkw 0x12480000166b5000 0x8249000002cd6a00 0x7fc000001ffff807 0xaff8000003ffff00

def z98 : W := mkw 0x408088e1609022e8 0x0810111c2c12045d 0x000018e3e00007f8 0x4000031c7c0000ff

def z99 : W := mkw 0x0c2e160292030000 0x0185c2c052406000 0xfc3e1f03ff038007 0x7f87c3e07fe07000

def z100 : W := mkw 0x9a66630e0e4d9c14 0x934ccc61c1c9b382 0x3c46671c0f0d9801 0x0788cce381e1b300

def z101 : W := mkw 0x082c000012030000 0x0105800002406000 0xfc3e00001f038007 0x3f87c00003e07000

def z102 : W := mkw 0x2d3f1702bb23c570 0x05a7e2e0576478ae 0xffbf9f03fff3e7ff 0xfff7f3e07ffe7cff

def z103 : W := mkw 0x9ffd5c90d66b5000 0xd3ffab921acd6a00 0x5fb81800f7700004 0x0bf703001eee0000

def z104 : W := mkw 0x164015340dcc0700 0x22c802a681b980e0 0x3c4007fc0f8c0603 0xe78800ff81f180c0

def z105 : W := mkw 0x2c2617028b018510 0x0584c2e0516030a2 0x3c0607000f018001 0x0780c0e001e03000

def z106 : W := mkw 0x41990880703240e0 0x083321100e06481c 0x43b81800f07001c4 0x087703001e0e0038

def z107 : W := mkw 0x9ff7ffdbc9000500 0x53fefffb792000a0 0xffffffffff0007c7 0xffffffffffe000f8

def z108 : W := mkw 0xd3d1c8e144f87288 0x9a7a391c289f0e51 0x03c1e0e000fc7800 0x80783c1c001f8f00

def z109 : W := mkw 0xbf7f5702bb038570 0x17efeae0576070ae 0xffffff03ff0387ff 0xffffffe07fe070ff

def z110 : W := mkw 0x93d1e8d944685000 0xd27a3d1b288d0a00 0x03c1e0fc00fc7800 0x80783c1f801f8f00

def z111 : W := mkw 0x2c2e370ebb078d74 0x0585c6e1d760f1ae 0xfc7e7f1fff0f9fff 0x7f8fcfe3ffe1f3ff

def z112 : W := mkw 0x8824400002011000 0x9104880000402200 0x0006600000019800 0x0000cc0000003300

def z113 : W := mkw 0x0008000012030000 0x0001000002406000 0x600000001f038000 0x2c00000003e07000

def z114 : W := mkw 0x0482bedbc0000000 0x409057db78000000 0x00001fffe0000000 0x400003fffc000000

def z115 : W := mkw 0x12c008b404dc0280 0x22580116809b8050 0x03c000fc00fc0000 0x8078001f801f8000

def z116 : W := mkw 0x008008a000900280 0x0010011400120050 0x438018e010f007c6 0xe870031c021e00f8

def z117 : W := mkw 0x019188c140000000 0x0032311828000000 0x83b998e3e0000006 0xd077331c7c000000

def z118 : W := mkw 0xdffffefbf0b262e8 0x5bffffdf7e164c5d 0xdffffffff0f267ff 0xfbfffffffe1e4cff

def z119 : W := mkw 0x419988c1703260e8 0x083331182e064c1d 0xc3b99803f07261fc 0x187733007e0e4c3f

def z120 : W := mkw 0x0c26b64b80000000 0x0184d6c970000000 0x9c7fffffe0000007 0xd38ffffffc000000

def z121 : W := mkw 0x9ff7fedbc0000000 0x53feffdb78000000 0x1fb81fffe0000004 0x43f703fffc000000

def z122 : W := mkw 0x9e6455140f4d1500 0xb3cc8aa281e9a2a0 0x3c46671c0f0d9801 0x0788cce381e1b300

def z123 : W := mkw 0x000001240884ae1c 0x00000024811095c3 0xa047e000088ffe3b 0xb408fc000111ffc7

def z124 : W := mkw 0x0000012408840600 0x00000024811080c0 0x204007fc088c0603 0xe40800ff811180c0

def z125 : W := mkw 0x9b7d4000166b5000 0x936fa80002cd6a00 0x7ff800001ffc0007 0xafff000003ff8000

def z126 : W := mkw 0x0000a16d08842e0c 0x0000142da11085c1 0x2041e7fc088c7e03 0xe4083cff81118fc0

def z127 : W := mkw 0x0008000030020060 0x000100000600400c 0x80380003e0020038 0x100700007c004007

def z128 : W := mkw 0x4119806170a26268 0x0823300c2e144c4d 0x803980e3e082663a 0xf007301c7c104cc7

def z129 : W := mkw 0x282ea24bb203a87c 0x0505d4497640750f 0x803fe003e003f838 0x1007fc007c007f07

def z130 : W := mkw 0x0002032608848610 0x00004064c11090c2 0xa04607ff088f863b 0xf408c0ffe111f0c7

def z131 : W := mkw 0x0000012409940780 0x20000024813280f0 0x00000000000007c0 0x00000000000000f8

def z132 : W := mkw 0x93d1e8d940000000 0x527a3d1b28000000 0x03c1e0fc00000000 0x80783c1f80000000

def z133 : W := mkw 0x000aa36f1eeffe1c 0x8001546de3ddffc3 0xe047e7ff1ffffe3b 0xfc08fcffe3ffffc7

def z134 : W := mkw 0x9b7d4000166b5000 0x936fa80002cd6a00 0xdfffe00017700007 0x9bfffc0002ee0000

def z135 : W := mkw 0x2000010029008570 0x04000020052010ae 0x00000000000007f8 0x00000000000000ff

def z136 : W := mkw 0x00080000166b5000 0x8001000002cd6a00 0x600000001ffff800 0x2c00000003ffff00

def z137 : W := mkw 0x9ff7ffffcddc0780 0x73fefffff9bb80f0 0xfffffffffffc07c7 0xffffffffffff80f8

def z138 : W := mkw 0x893d400012235000 0x9127a80002446a00 0x803fe0000003f800 0x1007fc0000007f00

def z139 : W := mkw 0x9e66761a80000000 0x53cccec350000000 0x1c46671c00000001 0x0388cce380000000

def z140 : W := mkw 0x04801c9001100180 0x2090039200220030 0x00001800000001c0 0x0000030000000038

def z141 : W := mkw 0x008808a0309202e0 0x001101140612405c 0xc3b818e3f0f207fe 0xf877031c7e1e40ff

def z142 : W := mkw 0x000001240884ae1c 0x00000024811095c3 0x204007fc088ffe3b 0xe40800ff8111ffc7

def z143 : W := mkw 0x9b75400006695000 0x936ea80000cd2a00 0x3fc7e0000ffdf801 0x87f8fc0001ffbf00

def z144 : W := mkw 0xdbfd4880767b50e0 0x9b7fa9100ecf6a1c 0x5fb81800f77001c4 0x0bf703001eee0038

def z145 : W := mkw 0x9b7d400010224000 0x136fa80002044800 0xdfffe00010f26007 0xbbfffc00021e4c00

def z146 : W := mkw 0xdb7dc041766b7068 0x9b6fb8082ecd6e0d 0xffffe003fffff83f 0xbffffc007fffff07

def z147 : W := mkw 0x9b7d41241fff5780 0xb36fa82483ffeaf0 0xffffe0001fffffc7 0xbffffc0003fffff8

def z148 : W := mkw 0x419188e140b06288 0x0832311c28160c51 0x038180e000f06000 0x8070301c001e0c00

def z149 : W := mkw 0x0824000002010000 0x0104800000402000 0x3c0600000f018001 0x0780c00001e03000

def z150 : W := mkw 0x9ff7fedbc000a81c 0x53feffdb78001503 0x9fffffffe003f83f 0xd3fffffffc007f07

def z151 : W := mkw 0x0000806100802208 0x0000100c20100441 0x800180e30082663a 0xf000301c60104cc7

def z152 : W := mkw 0x419baaeb70b262e8 0x0833755d6e164c5d 0xc3fffffff0f267ff 0xf87ffffffe1e4cff

def z153 : W := mkw 0x2c261702ab018570 0x0584c2e0556030ae 0x3c061f03ef0187f9 0x4780c3e07de030ff

def z154 : W := mkw 0x56c81db43dfe67e8 0x2ad903b687bfccfd 0x7fc01ffc1ffe67ff 0xeff803ff83ffccff

def z155 : W := mkw 0x459bbefbf0b262e8 0x48b377df7e164c5d 0xc3b99ffff0f267fe 0xf87733fffe1e4cff

def z156 : W := mkw 0x008008a000900280 0x0010011400120050 0x000018e0000007c0 0x4000031c000000f8

def z157 : W := mkw 0xdbfdc8e156fb7288 0x9b7fb91c2adf6e51 0xffffe0e01ffff807 0xbffffc1c03ffff00

def z158 : W := mkw 0x040015240ddc0780 0x208002a481bb80f0 0x7c001f001ffc07c7 0x6f8003e003ff80f8

def z159 : W := mkw 0x0482bfff0994af9c 0x209057ffe13295f3 0x00001fff000007f8 0x400003ffe00000ff

def z160 : W := mkw 0x16c2bfff0ddcaf9c 0x22d857ffe1bb95f3 0xffc7ffff1fffffff 0xfff8ffffe3ffffff

def z161 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z162 : W := mkw 0x4119804170226068 0x082330082e044c0d 0x80398003e0026038 0x100730007c004c07

def z163 : W := mkw 0x0002a36f0884ae1c 0x0000546de11095c3 0x204007ff088c063b 0xe40800ffe11180c7

def z164 : W := mkw 0x1ee61e9280000000 0x03dcc3d250000000 0x9ffe1fffe0000007 0xd3ffc3fffc000000

def z165 : W := mkw 0x0402160280000000 0x008042c050000000 0x00001f03e0000000 0x400003e07c000000

def z166 : W := mkw 0xdff7fefbe09022e8 0x5bfeffdf7c12045d 0x9fffffffe00007ff 0xd3fffffffc0000ff

def z167 : W := mkw 0xbe6e771abb038570 0x57cdcee3576070ae 0xfc7e7f1fff0387ff 0x7f8fcfe3ffe070ff

def z168 : W := mkw 0x16c81db41fff5780 0xa2d903b683ffeaf0 0x7fc01ffc1fffffc7 0xeff803ff83fffff8

def z169 : W := mkw 0x16c2bfff0ddcaf9c 0x22d857ffe1bb95f3 0x7fc01fff1ffc07ff 0xeff803ffe3ff80ff

def z170 : W := mkw 0x9b7d4000366b5060 0x936fa80006cd6a0c 0xfffff803ffffffff 0xffffff007fffffff

def z171 : W := mkw 0x0000a06d00842a0c 0x0000140da0108541 0x8041e0ff008e7e3a 0xf0083c1fe011cfc7

def z172 : W := mkw 0x93d1e8d940000000 0x527a3d1b28000000 0x83f9f8ffe0000006 0xd07f3f1ffc000000

def z173 : W := mkw 0xbfffffffffdf87f0 0x77fffffffffbf0fe 0xffffffffffff87ff 0xfffffffffffff0ff

def z174 : W := mkw 0x53d988e174fa62e8 0x0a7b311c2e9f4c5d 0xfff998e3fffe67ff 0xffff331c7fffccff

def z175 : W := mkw 0x9bfdc8c1566b5000 0x937fb9182acd6a00 0xfffff8e3fffff807 0xffffff1c7fffff00

def z176 : W := mkw 0x0002a36f0884ae1c 0x0000546de11095c3 0x8047e7ff0000063b 0xd008fcffe00000c7

def z177 : W := mkw 0x419188e160b062e8 0x0832311c2c160c5d 0x038198e3e0f067f8 0xc070331c7c1e0cff

def z178 : W := mkw 0xbffffffffb87af7c 0x57ffffffff70f5ef 0xffffffffff8fffff 0xfffffffffff1ffff

def z179 : W := mkw 0x000001240ddc0780 0x2000002481bb80f0 0x604007fc1ffc07c3 0xec0800ff83ff80f8

def z180 : W := mkw 0x008008a000900280 0x0010011400120050 0x038000e000f00000 0x8070001c001e0000

def z181 : W := mkw 0x16c01c9000000000 0x02d8039200000000 0x1fc01ffc00000007 0xc3f803ff80000000

def z182 : W := mkw 0x9b75400000000000 0x136ea80000000000 0x9fffe00000000007 0x93fffc0000000000

def z183 : W := mkw 0x9e64541080000000 0x53cc8a8210000000 0x1c00000000000000 0x0380000000000000

def z184 : W := mkw 0x0000000004685000 0x80000000008d0a00 0x0000000000fc7800 0x00000000001f8f00

def z185 : W := mkw 0x9b75400004685000 0x936ea800008d0a00 0x9fffe00000fc7807 0x93fffc00001f8f00

def z186 : W := mkw 0x9ff7ffffc9940780 0x73fefffff93280f0 0x9fffffffe00007c7 0xd3fffffffc0000f8

def z187 : W := mkw 0x9f7f5602966b5000 0x93efeac052cd6a00 0xffffff03fffff807 0xffffffe07fffff00

def z188 : W := mkw 0x9b7d4000166b5000 0x936fa80002cd6a00 0xbc7fe0000f0ff801 0x178ffc0001e1ff00

def z189 : W := mkw 0x6dbfbfeffbb7effc 0x0db7f7fdff76fdff 0xffffffffffffffff 0xffffffffffffffff

def z190 : W := mkw 0x2826020282018010 0x0504c04050403002 0x0006000000018000 0x0000c00000003000

def z191 : W := mkw 0x2c26b76f8b85af1c 0x0584d6edf170b5e3 0xbc47e7ff0f8ffe3b 0xf788fcffe1f1ffc7

def z192 : W := mkw 0x082ea36f1a87ae1c 0x0105d46de350f5c3 0xfc7fe7ff1f8ffe3f 0xff8ffcffe3f1ffc7

def z193 : W := mkw 0x56c09df56ddc27e8 0x2ad813beadbb84fd 0x7fc01ffffffc07ff 0xeff803ffffff80ff

def z194 : W := mkw 0x40000020209022e8 0x080000040412045d 0x00000000000007f8 0x00000000000000ff

def z195 : W := mkw 0x9ff7feffc4dc0280 0x73feffdff89b8050 0x9fffffffe0fc0007 0xd3fffffffc1f8000

def z196 : W := mkw 0x0002030208008410 0x0000406041001082 0xa00607030803863b 0x7400c0e0610070c7

def z197 : W := mkw 0x0002230e08048c14 0x00004461c1009182 0x0000071c00000000 0x000000e380000000

def z198 : W := mkw 0x53d188f544fc6288 0x2a7a311ea89f8c51 0x03c180fc00fc6000 0x8078301f801f8c00

def z199 : W := mkw 0x0119000030224060 0x002320000604480c 0xc3b99803f0f267fe 0xf87733007e1e4cff

def z200 : W := mkw 0x9ff7feffc0842a0c 0x53feffdff8108541 0x9fffffffe08c7807 0xd3fffffffc118f00

def z201 : W := mkw 0x9b7fe36f1eeffe1c 0x936ffc6de3ddffc3 0xffffe7ff1ffffe3f 0xfffffcffe3ffffc7

def z202 : W := mkw 0x04801db409940780 0x209003b6813280f0 0x20401ffc088c07c3 0xe40803ff811180f8

def z203 : W := mkw 0x9ff55c90c5580180 0x73feab9218ab0030 0x5fb81800f77001c4 0x0bf703001eee0038

def z204 : W := mkw 0x693f8243f223e078 0x0d27f0487e447c0f 0x803f8003e003e038 0x1007f0007c007c07

def z205 : W := mkw 0x9ff5fcd9c0000000 0x53febf9b38000000 0x1ff9f8fce0000004 0x83ff3f1f9c000000

def z206 : W := mkw 0x0002030208008410 0x0000406041001082 0xa047e703088ffe3b 0xf408fce06111ffc7

def z207 : W := mkw 0x0c26b76f8884ae1c 0x0184d6edf11095c3 0xbc7fffffe88ffe3f 0xf78ffffffd11ffc7

def z208 : W := mkw 0x16c01d9009000500 0x02d803b2012000a0 0x7fc01ffc1f0007c7 0xeff803ff83e000f8

def z209 : W := mkw 0x9351400004685000 0x926a2800008d0a00 0x7fc1e0001ffc7807 0xaff83c0003ff8f00

def z210 : W := mkw 0x164015140d4c0500 0x22c802a281a980a0 0x3c40071c0f0c0001 0x078800e381e18000

def z211 : W := mkw 0x9b7fe24bd66b5000 0xd36ffc497acd6a00 0xffffe003fffff807 0xbffffc007fffff00

def z212 : W := mkw 0x9a64400000000000 0x134c880000000000 0x1c46600000000001 0x0388cc0000000000

def z213 : W := mkw 0x16c2bfffcddc0780 0x62d857fff9bb80f0 0x7fc01ffffffc07c7 0xeff803ffffff80f8

def z214 : W := mkw 0x9ffffedbd2235000 0xd3ffffdb7a446a00 0x9fffffffe003f807 0xd3fffffffc007f00

def z215 : W := mkw 0x01190000166b5000 0x8023200002cd6a00 0xe3b980001ffff806 0xbc77300003ffff00

def z216 : W := mkw 0x0000000000000000 0x0000000000000000 0x20400000088c0003 0xa408000001118000

def z217 : W := mkw 0x12c0089004580080 0x22580112008b0010 0x0380000000700000 0x00700000000e0000

def z218 : W := mkw 0x89b7eacbc0000000 0x5136fd5978000000 0x83bff8e3e0000006 0xd077ff1c7c000000

def z219 : W := mkw 0x419908a070b242e0 0x083321140e16485c 0x43b818e0f0f007c6 0xe877031c1e1e00f8

def z220 : W := mkw 0x2c2c1400b3030160 0x058582801660602c 0xdc381803f70207fe 0x7b8703007ee040ff

def z221 : W := mkw 0x0400150009000500 0x008002a0012000a0 0x7c001f001f0007c7 0x6f8003e003e000f8

def z222 : W := mkw 0x3eee1fb6bfdf87f0 0x27ddc3f6d7fbf0fe 0xfffe1fffffff87ff 0xffffc3fffffff0ff

def z223 : W := mkw 0x20020202a0008070 0x040040405400100e 0x00000003e0000038 0x000000007c000007

def z224 : W := mkw 0x9ee6fedbc0000000 0x53dcdfdb78000000 0x1c467fffe0000001 0x4388cffffc000000

def z225 : W := mkw 0xbe6e5702bf4b9570 0x97cdcae057e972ae 0xfc7e7f03ff0f9fff 0x7f8fcfe07fe1f3ff

def z226 : W := mkw 0x4482befbe09022e8 0x489057df7c12045d 0x00001fffe00007f8 0x400003fffc0000ff

def z227 : W := mkw 0x16c23fbe0ddc8f94 0x22d847f7c1bb91f2 0x7fc67ffc1ffd9fc7 0xeff8cfff83ffb3f8

def z228 : W := mkw 0x9bfd48a016fb5280 0x937fa91402df6a50 0xfffff8e01fffffc7 0xffffff1c03fffff8

def z229 : W := mkw 0xbe6657028f499510 0x97cccae051e932a2 0x3c4667000f0d9801 0x0788cce001e1b300

def z230 : W := mkw 0x9bf5c8c140000000 0x137eb91828000000 0x9ffff8e3e0000007 0xd3ffff1c7c000000

def z231 : W := mkw 0x0000000000000000 0x0000000000000000 0x8047e00000000003 0x9008fc0000000000

def z232 : W := mkw 0x0080088000000000 0x0010011000000000 0x038018e000000006 0xc070031c00000000

def z233 : W := mkw 0x400801243dfe67e8 0x2801002487bfccfd 0x600000001ffe67f8 0x2c00000003ffccff

def z234 : W := mkw 0x9351e06d04ec7a0c 0x926a3c0da09d8f41 0x03c1e0fc00fc7800 0x80783c1f801f8f00

def z235 : W := mkw 0x0000000000000000 0x0000000000000000 0x7c0000001f000007 0x2f80000003e00000

def z236 : W := mkw 0x0000000000000000 0x0000000000000000 0x80381803e0000006 0x500703007c000000

def z237 : W := mkw 0x419908a070b262e8 0x083321140e164c5d 0x43b81800f0f267fc 0x287703001e1e4cff

def z238 : W := mkw 0x0000000000000000 0x0000000000000000 0x4380000010f00006 0xa8700000021e0000

def z239 : W := mkw 0xbf7f57029f6bd510 0x97efeae053ed7aa2 0xffffe7001ffff807 0xbffffce003ffff00

def z240 : W := mkw 0xc93dc04172237068 0x9927b8082e446e0d 0x803fe003e003f838 0x1007fc007c007f07

def z241 : W := mkw 0x0000010408040400 0x0000002081008080 0x2040071c080c0001 0x040800e381018000

def z242 : W := mkw 0x893fe36f1aa7fe1c 0x9127fc6de354ffc3 0xa07fe7ff088ffe3b 0xf40ffcffe111ffc7

def z243 : W := mkw 0x9f77560280000000 0x13eeeac050000000 0x9fffff03e0000007 0xd3ffffe07c000000

def z244 : W := mkw 0x9ff75e92c0000000 0x53feebd258000000 0x9fbe1f03e0000007 0x53f7c3e07c000000

def z245 : W := mkw 0x0000806100802208 0x0000100c20100441 0x000000e300000638 0x4000001c600000c7

def z246 : W := mkw 0x9ff77e9ac0000000 0x53feefd358000000 0x1ffe7f1ce0000005 0x03ffcfe39c000000

def z247 : W := mkw 0x9e66761a86491000 0xd3cccec350c92200 0x3c46671c0f0d9801 0x0788cce381e1b300

def z248 : W := mkw 0x0000000000000000 0x0000000000000000 0x004007fc00000003 0xc00800ff80000000

def z249 : W := mkw 0x0119806110a26208 0x0023300c22144c41 0xc3b980e310f2663e 0xf877301c621e4cc7

def z250 : W := mkw 0x4008000030226068 0x0801000006044c0d 0x0000000000026038 0x0000000000004c07

def z251 : W := mkw 0x9ff7fedbc4480000 0x53feffdb78890000 0xfffffffffffc0007 0xffffffffffff8000

def z252 : W := mkw 0x9b7f630e1e6fdc14 0x936fec61c3cdfb82 0xffffe71c1ffff807 0xbffffce383ffff00

def z253 : W := mkw 0x8937e24bc0000000 0x5126fc4978000000 0x807fe7ffe0000003 0xd00ffcfffc000000

def z254 : W := mkw 0x0082abef0894ae9c 0x0010557de11295d3 0xe3c7ffff18ffffff 0xfc78ffffe31fffff

def z255 : W := mkw 0x1eec1db41fdf0780 0x23dd83b683fbe0f0 0xfffe1ffc1fff87c7 0xffffc3ff83fff0f8

def z256 : W := mkw 0x6c2e1722bbb3e7f8 0x0d85c2e457767cff 0xfc3e1f03fff3e7ff 0x7f87c3e07ffe7cff

def z257 : W := mkw 0x57d99cf175fa63e8 0x2afb339e2ebf4c7d 0xdfb998e3f7f267fe 0xfbf7331c7efe4cff

def z258 : W := mkw 0x9ff7ffffc884ae1c 0x53fefffff91095c3 0x9fffffffe000063f 0xd3fffffffc0000c7

def z259 : W := mkw 0xdffddcf1f0b262e8 0x5bffbb9e3e164c5d 0xdfb998e3f0f267fe 0xfbf7331c7e1e4cff

def z260 : W := mkw 0x0119000010224000 0x0023200002044800 0x8039800000026000 0x1007300000004c00

def z261 : W := mkw 0x408088e140902288 0x0810111c28120451 0x000000e000000000 0x0000001c00000000

def z262 : W := mkw 0x16c01db40ddc0780 0x22d803b681bb80f0 0x03c01ffc00fc07c0 0xc07803ff801f80f8

def z263 : W := mkw 0x093d000012234000 0x0127a00002446800 0xffbf80001ff3e007 0xbff7f00003fe7c00

def z264 : W := mkw 0x419988e176fb72e8 0x8833311c2edf6e5d 0xe3b998e3fffffffe 0xfc77331c7fffffff

def z265 : W := mkw 0x2c2eb74bbb03ad7c 0x0585d6e9776075af 0xfc3fff03ff03ffff 0x7f87ffe07fe07fff

def z266 : W := mkw 0x24021702a9008570 0x048042e0552010ae 0xa0061f03e80387fb 0x7400c3e07d0070ff

def z267 : W := mkw 0x0402170209008510 0x008042e0412010a2 0xfc061f031f0387ff 0x7f80c3e063e070ff

def z268 : W := mkw 0x408088e1609022e8 0x0810111c2c12045d 0x800198e3e08267fa 0xf000331c7c104cff

def z269 : W := mkw 0xad3f5702bb23d570 0x95a7eae057647aae 0xfc3fff03ff03ffff 0x7f87ffe07fe07fff

def z270 : W := mkw 0x240a1702b9028570 0x048142e0572050ae 0xc0381f03f00207fe 0x780703e07e0040ff

def z271 : W := mkw 0x17d19df54ddc0780 0x22fa33bea9bb80f0 0xfff99ffffffc07c7 0xffff33ffffff80f8

def z272 : W := mkw 0x0000010008000400 0x0000002001000080 0x2000070008000603 0x640000e0010000c0

def z273 : W := mkw 0x2c2e1726bb87af7c 0x0585c2e4d770f5ef 0xfc3e1f03ff8fffff 0x7f87c3e07ff1ffff

def z274 : W := mkw 0x8d37f64bc0000000 0x51a6fec978000000 0x9c3fff03e0000007 0x5387ffe07c000000

def z275 : W := mkw 0x1640141000000000 0x02c8028200000000 0x1c40071c00000001 0x038800e380000000

def z276 : W := mkw 0x124001240ccc0600 0x02480024819980c0 0x7fc007fc1ffc0607 0xeff800ff83ff80c0

def z277 : W := mkw 0x9ff7fedbc5580180 0x73feffdb78ab0030 0xdffffffff77001c7 0xdbfffffffeee0038

def z278 : W := mkw 0x282e0302bb038570 0x0505c060576070ae 0xe03e0003ff0387f8 0x3c07c0007fe070ff

def z279 : W := mkw 0x16c81db43dde07e0 0x22d903b687bbc0fc 0xfff81ffffffe07ff 0xffff03ffffffc0ff

def z280 : W := mkw 0x082c0000166b5000 0x8105800002cd6a00 0xfc3e00001ffff807 0x3f87c00003ffff00

def z281 : W := mkw 0x0000010408048c14 0x0000002081009182 0x20000000080d9800 0x040000000101b300

def z282 : W := mkw 0x2c2c1500bb038570 0x058582a0176070ae 0x7c381800ff0387fc 0x2f8703001fe070ff

def z283 : W := mkw 0x12c008b404dc0280 0x22580116809b8050 0x7fc000fc1ffc0007 0xaff8001f83ff8000

def z284 : W := mkw 0x1a6c0000164b0000 0x034d800002c96000 0xfffe00001fff8007 0xbfffc00003fff000

def z285 : W := mkw 0x9ff55c9000000000 0x13feab9200000000 0x9ffffffc00000007 0xd3ffffff80000000

def z286 : W := mkw 0xc93fe24bf0226068 0x5927fc497e044c0d 0x803fe003e0026038 0x1007fc007c004c07

def z287 : W := mkw 0x282c0000b2030060 0x050580001640600c 0x00380000e0000000 0x000700001c000000

def z288 : W := mkw 0x9ffd5db41fff5780 0xb3ffabb683ffeaf0 0x7ff81ffc1ffc07c7 0xefff03ff83ff80f8

def z289 : W := mkw 0x9b7d400012235000 0x936fa80002446a00 0x9fffe0000003f807 0x93fffc0000007f00

def z290 : W := mkw 0x9b7dc06116eb7208 0x936fb80c22dd6e41 0xffffe0e31ffffe3f 0xfffffc1c63ffffc7

def z291 : W := mkw 0x4119806170b262e8 0x0823300c2e164c5d 0xc0398003f0f267f8 0x380730007e1e4cff

def z292 : W := mkw 0x0000002000802208 0x0000000400100441 0x0000000000826638 0x2000000000104cc7

def z293 : W := mkw 0x36c21fb6addc87f0 0x26d843f6d5bb90fe 0x7fc01ffffffc07ff 0xeff803ffffff80ff

def z294 : W := mkw 0x0002a36f08840600 0x0000546de11080c0 0xa047e7ff088c0603 0xf408fcffe11180c0

def z295 : W := mkw 0x2c2e9763bb83a778 0x0585d2ec777074ef 0xfc3f9fe3ff83e7ff 0xff87f3fc7ff07cff

def z296 : W := mkw 0x2c2c1400b3030160 0x058582801660602c 0xfc3e1800ff0381c7 0x3f87c3001fe07038

def z297 : W := mkw 0x1642371e0d4c8d14 0x22c846e3c1a991a2 0x3c46671c0f0d9801 0x0788cce381e1b300

def z298 : W := mkw 0x57d91db47dfe47e0 0x2afb23b68fbfc8fc 0x7ff81ffcfffc07c7 0xefff03ff9fff80f8

def z299 : W := mkw 0x9e66f65b80000000 0x53ccdecb70000000 0x9c47e7ff00000003 0xd388fcffe0000000

def z300 : W := mkw 0x45999de179b267e8 0x08b333bc2f364cfd 0xffb99fe3fff267ff 0xfff733fc7ffe4cff

def z301 : W := mkw 0x2c2e1702bb038570 0x0585c2e0576070ae 0xbc3e0703ef038039 0x1787c0e07de07007

def z302 : W := mkw 0x000283630880a618 0x0000506c611014c3 0xa00787e30883e63b 0xf400f0fc61107cc7

def z303 : W := mkw 0x3ee61fb68fdd8790 0x27dcc3f6d1fbb0f2 0x7fc61ffc1ffd87c7 0xeff8c3ff83ffb0f8

def z304 : W := mkw 0x0000000004480000 0x0000000000890000 0x600000001ffc0000 0x2c00000003ff8000

def z305 : W := mkw 0x0080a8d940000000 0x4010151b28000000 0x000000fc00000000 0x0000001f80000000

def z306 : W := mkw 0x41990880703240e0 0x083321100e06481c 0xc3b81803f07207fe 0x787703007e0e40ff

def z307 : W := mkw 0x9b77e24b00000000 0x136efc4960000000 0x9fffe7ff00000007 0xd3fffcffe0000000

def z308 : W := mkw 0x9ee67e9a80000000 0x53dccfd350000000 0x1fc67ffc00000007 0xc3f8cfff80000000

def z309 : W := mkw 0x411ba24b7022e87c 0x082374496e045d0f 0x803fe003e003f838 0x1007fc007c007f07

def z310 : W := mkw 0x082c000012030000 0x0105800002406000 0x803e000000038000 0x1007c00000007000

def z311 : W := mkw 0x9bf5e8d940000000 0x537ebd1b28000000 0x9fffe0fc00000007 0x93fffc1f80000000

def z312 : W := mkw 0x0400140001000100 0x0080028000200020 0x5c001800170001c4 0x0b80030002e00038

def z313 : W := mkw 0xbff7ffdbe9008570 0x57fefffb7d2010ae 0x9fffffffe00007ff 0xd3fffffffc0000ff

def z314 : W := mkw 0x0400150009000500 0x008002a0012000a0 0x00001f00000007c0 0x400003e0000000f8

def z315 : W := mkw 0x019988c150224000 0x003331182a044800 0xc3b998e3f0f26006 0xf877331c7e1e4c00

def z316 : W := mkw 0xdffffffff8b6eefc 0x5bffffffff16dddf 0xfffffffff8ffffff 0xffffffffff1fffff

def z317 : W := mkw 0x2008000032038070 0x040100000640700e 0x0000000000038038 0x0000000000007007

def z318 : W := mkw 0x16c2bedb00000000 0x02d857db60000000 0x9fc7ffff00000007 0xd3f8ffffe0000000

def z319 : W := mkw 0x0000000000000000 0x0000000000000000 0x800000030002063a 0x70000000600040c7

def z320 : W := mkw 0x53d988f574fe62e8 0x2a7b311eae9fcc5d 0xc3f998fff0fe67fe 0xf87f331ffe1fccff

def z321 : W := mkw 0xbb7f4202b66bd070 0x976fe84056cd7a0e 0xffffe003fffff83f 0xbffffc007fffff07

def z322 : W := mkw 0x1642b77f0dccaf1c 0x22c856efe1b995e3 0xbc47e7ff0f8ffe3b 0xf788fcffe1f1ffc7

def z323 : W := mkw 0x0002a26f00842a0c 0x0000544de0108541 0x8047e7ff008c7803 0xd008fcffe0118f00

def z324 : W := mkw 0x9f77761a80000000 0x53eeeec350000000 0x9fffe71c00000007 0x93fffce380000000

def z325 : W := mkw 0x0193abef4884ae1c 0x0032757de91095c3 0xa3ffffffe88ffe3f 0xf47ffffffd11ffc7

def z326 : W := mkw 0x9e66f77f8884ae1c 0x53ccdeeff11095c3 0xbc47e7ff088ffe3b 0xf788fcffe111ffc7

def z327 : W := mkw 0x008009a40ddc0780 0x2010013481bb80f0 0x638018e01ffc07c6 0xec70031c03ff80f8

def z328 : W := mkw 0x408888e170b262e8 0x0811111c2e164c5d 0x400018e3f0f267f8 0x6800031c7e1e4cff

def z329 : W := mkw 0x893d400012235000 0x9127a80002446a00 0xfc3fe0001f03f807 0x3f87fc0003e07f00

def z330 : W := mkw 0x0000200c00040804 0x0000040180008100 0x0040601c000c1800 0x00080c0380018300

def z331 : W := mkw 0x9f7d55141f6f5500 0xb3efaaa283edeaa0 0xffffe71c1ffff807 0xbffffce383ffff00

def z332 : W := mkw 0x4008002030b262e8 0x0801000406164c5d 0xc0381803f0f267fe 0x780703007e1e4cff

def z333 : W := mkw 0x93d1e8fd40842a0c 0x527a3d1fa8108541 0x03c1e0fc008c7800 0x80783c1f80118f00

def z334 : W := mkw 0x282e0302ba038470 0x0505c0605740708e 0xa03e0703e803863b 0x7407c0e07d0070c7

def z335 : W := mkw 0x16c01c9000000000 0x02d8039200000000 0x1f80180000000004 0x03f0030000000000

def z336 : W := mkw 0x17d91db41dfe4780 0x22fb23b683bfc8f0 0xfff99ffc1ffe67c7 0xffff33ff83ffccf8

def z337 : W := mkw 0x2402b76fa984af7c 0x048056edf53095ef 0x00001fffe00007f8 0x400003fffc0000ff

def z338 : W := mkw 0x9ffd5c90d66b5000 0xd3ffab921acd6a00 0xfffff800fffff807 0xbfffff001fffff00

def z339 : W := mkw 0x2c2e1702bb038570 0x0585c2e0576070ae 0x7c0607001f0387f9 0x2f80c0e003e070ff

def z340 : W := mkw 0x0000000000000000 0x0000000000000000 0x40001800100007c6 0x68000300020000f8

def z341 : W := mkw 0x3e6e1716bf4f8570 0x27cdc2e2d7e9f0ae 0xfc7e1f1fff0f87ff 0x7f8fc3e3ffe1f0ff

def z342 : W := mkw 0x0000a16d0884ae1c 0x0000142da11095c3 0x2041e0fc088ffe38 0xa4083c1f8111ffc7

def z343 : W := mkw 0x1ee61fb68ddc0780 0x23dcc3f6d1bb80f0 0xfffe1ffffffc07c7 0xffffc3ffffff80f8

def z344 : W := mkw 0x419b8be378b2e6f8 0x0833717c6f165cdf 0xe3bf9fe3f8f3e7ff 0xfc77f3fc7f1e7cff

def z345 : W := mkw 0x9ff7ffdbc8008410 0x53fefffb79001082 0xbfffffffe803863f 0xf7fffffffd0070c7

def z346 : W := mkw 0xbfff5f92fb038570 0x57ffebf25f6070ae 0xffbe1f03ff0387ff 0x7ff7c3e07fe070ff

def z347 : W := mkw 0x000aa36f3886ae7c 0x0001546de710d5cf 0xe07ffffff88fffff 0xfc0fffffff11ffff

def z348 : W := mkw 0x9240601800000000 0x52480c0300000000 0x0040601c00000000 0x00080c0380000000

def z349 : W := mkw 0x419188e140b06288 0x0832311c28160c51 0x438198e010f067c6 0xe870331c021e0cf8

def z350 : W := mkw 0x0000002000900280 0x0000000400120050 0x4000000010f007c0 0x28000000021e00f8

def z351 : W := mkw 0x4082abef6894aefc 0x0810557ded1295df 0x00001fffe00007f8 0x400003fffc0000ff

def z352 : W := mkw 0x0408150039020560 0x008102a0072040ac 0xfc381f03ff0207ff 0x7f8703e07fe040ff

def z353 : W := mkw 0x400aa36f38b6eefc 0x0801546de716dddf 0xe047e7ff18fffffb 0xfc08fcffe31fffff

def z354 : W := mkw 0x0002232e08848e14 0x00004465c11091c2 0x204667fc088d9e03 0xe408ccff8111b3c0

def z355 : W := mkw 0xbe66771a8b018510 0x57cccee3516030a2 0x3c46671c0f018001 0x0788cce381e03000

def z356 : W := mkw 0x0593bedbc0000000 0x40b277db78000000 0x83b99fffe0000006 0xd07733fffc000000

def z357 : W := mkw 0x419988e170b262e8 0x0833311c2e164c5d 0xe3fff8e3f8ffffff 0xfc7fff1c7f1fffff

def z358 : W := mkw 0x0002a26f0084aa1c 0x0000544de0109543 0x8047e0ff008ff838 0x9008fc1fe011ff07

def z359 : W := mkw 0x2008000033030160 0x040100000660602c 0x40000000170001c0 0x0800000002e00038

def z360 : W := mkw 0x16c01d940d5c0580 0x22d803b281ab80b0 0x7fc01f1c1f7c01c5 0x0ff803e383ef8038

def z361 : W := mkw 0x0008000010224000 0x0001000002044800 0x4000000010f26000 0x28000000021e4c00

def z362 : W := mkw 0x8db7fedbc0000000 0x51b6ffdb78000000 0x803fffffe0000000 0x5007fffffc000000

def z363 : W := mkw 0x2402170289008510 0x048042e0512010a2 0x0000070000000000 0x000000e000000000

def z364 : W := mkw 0x9fffffff1fffff9c 0xb3ffffffe3fffff3 0xffffffff1fffffff 0xffffffffe3ffffff

def z365 : W := mkw 0x04801c90c0000000 0x4090039218000000 0x00001800e0000000 0x000003001c000000

def z366 : W := mkw 0x9b7d4000166b5000 0x936fa80002cd6a00 0x7fb800001ffff804 0x2ff7000003ffff00

def z367 : W := mkw 0x000203260884ae1c 0x00004064c11095c3 0xa0060703088ffe3b 0x7400c0e06111ffc7

def z368 : W := mkw 0x419989e578b666e8 0x0833313caf16ccdd 0xe3f99ffff8fe67ff 0xfc7f33ffff1fccff

def z369 : W := mkw 0xdbfd4880767b50e0 0x9b7fa9100ecf6a1c 0xfffff800fffff9c7 0xbfffff001fffff38

def z370 : W := mkw 0x9ffd5c90166b5000 0x93ffab9202cd6a00 0xfffffffc1ffff807 0xffffffff83ffff00

def z371 : W := mkw 0x164015340ddc0780 0x22c802a681bb80f0 0x7c40071c1ffc07c1 0x2f8800e383ff80f8

def z372 : W := mkw 0x16c01c9004480000 0x02d8039200890000 0x7fc01ffc1ffc0007 0xeff803ff83ff8000

def z373 : W := mkw 0x16c21fb60ddc8790 0x22d843f6c1bb90f2 0xffc61fff1fff87ff 0xfff8c3ffe3fff0ff

def z374 : W := mkw 0x9b7d4000166b5000 0x936fa80002cd6a00 0xdfbfe0001773f804 0x1bf7fc0002ee7f00

def z375 : W := mkw 0x0000010009000500 0x00000020012000a0 0x600000001f0007c0 0x2c00000003e000f8

def z376 : W := mkw 0x24821fb6a99487f0 0x249043f6d53290fe 0x00001fffe00007f8 0x400003fffc0000ff

def z377 : W := mkw 0x2c2c1500bb030560 0x058582a0176060ac 0x7c381f00ff0007c7 0x6f8703e01fe000f8

def z378 : W := mkw 0x893d400012235000 0x9127a80002446a00 0xa07fe000088ff803 0xb40ffc000111ff00

def z379 : W := mkw 0x0400152409840700 0x008002a4813080e0 0x7c401ffc1f8c07c7 0xef8803ff83f180f8

def z380 : W := mkw 0x41990880703240e0 0x083321100e06481c 0xc3b99800f0f261c6 0xb87733001e1e4c38

def z381 : W := mkw 0x419988e170b262e8 0x0833311c2e164c5d 0x83b980e3e0f26038 0x9077301c7c1e4c07

def z382 : W := mkw 0x4119804170226068 0x082330082e044c0d 0xc0399803f00267fe 0x780733007e004cff

def z383 : W := mkw 0x97d1fcd940000000 0x52fa3f9b28000000 0x1fc1fffc00000007 0xc3f83fff80000000

def z384 : W := mkw 0x93594000146a5000 0x926b2800028d4a00 0xc3f9e00010fe7806 0xb87f3c00021fcf00

def z385 : W := mkw 0x9ff55db40ddc0780 0x33feabb681bb80f0 0xfffffffc1ffc07c7 0xffffffff83ff80f8

def z386 : W := mkw 0xbffffedbf3030160 0x57ffffdb7e60602c 0xdffffffff70001c7 0xdbfffffffee00038

def z387 : W := mkw 0x082e03021a038410 0x0105c06043407082 0xfc3e07031f03863f 0x7f87c0e063e070c7

def z388 : W := mkw 0x0002230e08048c14 0x00004461c1009182 0xa047e71c088ff803 0xb408fce38111ff00

def z389 : W := mkw 0x16c01db40ddc0780 0x22d803b681bb80f0 0x5f801ffc177007c4 0x4bf003ff82ee00f8

def z390 : W := mkw 0x8826620a80000000 0x5104cc4150000000 0x0006600000000000 0x0000cc0000000000

def z391 : W := mkw 0x0002a26b0080aa1c 0x0000544d60101543 0x8007e0e30083fe3a 0xf000fc1c60107fc7

def z392 : W := mkw 0x1240000004480000 0x0248000000890000 0x5f80000017700004 0x0bf0000002ee0000

def z393 : W := mkw 0x9ff5dcd1c0000000 0x53febb9a38000000 0x9fb998e3e0000006 0xd3f7331c7c000000

def z394 : W := mkw 0x40080000303240e0 0x080100000606481c 0x40000000107001c0 0x08000000020e0038

def z395 : W := mkw 0x16c01db40ddcaf9c 0x22d803b681bb95f3 0x7fc01ffc1fffffff 0xeff803ff83ffffff

def z396 : W := mkw 0x0000000006491000 0x8000000000c92200 0x200000000f0d9800 0x0400000001e1b300

def z397 : W := mkw 0x282c01003b038570 0x05058020076070ae 0xfc3e00001f0387ff 0x3f87c00003e070ff

def z398 : W := mkw 0x0008000012235000 0x8001000002446a00 0x000000000003f800 0x0000000000007f00

def z399 : W := mkw 0x0c26170288008410 0x0184c2e051001082 0xbc3e1f03e803863f 0x7787c3e07d0070c7

def z400 : W := mkw 0x9ffffedbd0224000 0x53ffffdb7a044800 0xdffffffff0f26007 0xfbfffffffe1e4c00

def z401 : W := mkw 0x0002a36f0884ae1c 0x0000546de11095c3 0x200007ff088ffe38 0x640000ffe111ffc7

def z402 : W := mkw 0x16c01db408840600 0x02d803b6811080c0 0x3fc01ffc088c0607 0xe7f803ff811180c0

def z403 : W := mkw 0x0c26170289000500 0x0184c2e0512000a0 0xfc3e1f03ff0007c7 0x7f87c3e07fe000f8

def z404 : W := mkw 0x6dbd1c80f33341e0 0x0db7a3901e66683c 0x5fb81800f77001c4 0x0bf703001eee0038

def z405 : W := mkw 0x9ee67fbe8ddc0780 0x73dccff7d1bb80f0 0x7fc67ffc1ffc07c7 0xeff8cfff83ff80f8

def z406 : W := mkw 0x240815003b038570 0x048102a0076070ae 0x7c001f001f0387ff 0x6f8003e003e070ff

def z407 : W := mkw 0x2caebfdbfb038570 0x4595d7fb7f6070ae 0xfc3e1fffff0387ff 0x7f87c3ffffe070ff

def z408 : W := mkw 0x0002a36f0884ae1c 0x0000546de11095c3 0x8007e7ff0003fe38 0x5000fcffe0007fc7

def z409 : W := mkw 0x2402b76fa984af7c 0x048056edf53095ef 0xa047ffffe88ffffb 0xf408fffffd11ffff

def z410 : W := mkw 0x411ba36f78a6ee7c 0x0823746def14ddcf 0xa07fe7ffe88ffe3b 0xf40ffcfffd11ffc7

def z411 : W := mkw 0x164015140d4c0500 0x22c802a281a980a0 0x7c401f1c1f0c07c7 0x6f8803e383e180f8

def z412 : W := mkw 0x9ffffedbd2030000 0x53ffffdb7a406000 0xffffffffff038007 0xffffffffffe07000

def z413 : W := mkw 0xa93f4202b223d070 0x9527e84056447a0e 0x803fe003e003f838 0x1007fc007c007f07

def z414 : W := mkw 0x0000a06d00842a0c 0x0000140da0108541 0x000000fc00000000 0x0000001f80000000

def z415 : W := mkw 0x8937e36fc884ae1c 0x5126fc6df91095c3 0xa07fe7ffe88ffe3b 0xf40ffcfffd11ffc7

def z416 : W := mkw 0x57dbbfff7dfeeffc 0x2afb77ffefbfddff 0xffffffffffffffff 0xffffffffffffffff

def z417 : W := mkw 0x2c2eb76fbb87af7c 0x0585d6edf770f5ef 0xfc3e1fffff0387ff 0x7f87c3ffffe070ff

def z418 : W := mkw 0x9b7d4000166b5000 0x936fa80002cd6a00 0x83ffe00000fff800 0x907ffc00001fff00

def z419 : W := mkw 0x97d3fedbc0000000 0x52fa7fdb78000000 0x03c1ffffe0000000 0xc0783ffffc000000

def z420 : W := mkw 0x9a66e36f0ecdbe1c 0x934cdc6de1d9b7c3 0xbc47e7ff0f8ffe3b 0xf788fcffe1f1ffc7

def z421 : W := mkw 0x93d3eadb40000000 0x527a7d5b68000000 0x83c7e7ff00000003 0xd078fcffe0000000

def z422 : W := mkw 0x16c01db40ddc0780 0x22d803b681bb80f0 0x7f8018001ffc07c4 0x2ff0030003ff80f8

def z423 : W := mkw 0x9a6c4000164b1000 0x934d880002c96200 0xfc7e60001f0f9807 0x3f8fcc0003e1f300

def z424 : W := mkw 0x1240000004480000 0x0248000000890000 0xffc7e0001ffff807 0xbff8fc0003ffff00

def z425 : W := mkw 0x419188e140b06288 0x0832311c28160c51 0x838180e300f2663a 0xf070301c601e4cc7

def z426 : W := mkw 0x082c000012030000 0x0105800002406000 0x5c38000017000004 0x0b87000002e00000

def z427 : W := mkw 0x0000806100802208 0x0000100c20100441 0xa047e0e3088ffe3b 0xf408fc1c6111ffc7

def z428 : W := mkw 0x408088e1609022e8 0x0810111c2c12045d 0x438018e3f0f007fe 0xe870031c7e1e00ff

def z429 : W := mkw 0x2c2617028b018510 0x0584c2e0516030a2 0xbc3e1f03ef018007 0x5787c3e07de03000

def z430 : W := mkw 0x16c01cb405dc0380 0x22d8039680bb8070 0x5fc018fc17fc01c4 0x8bf8031f82ff8038

def z431 : W := mkw 0xbf7ff76fbfefff7c 0x97effeedf7fdffef 0xffffffffffffffff 0xffffffffffffffff

def z432 : W := mkw 0x0111804140000000 0x0022300828000000 0x80398003e0000000 0x100730007c000000

def z433 : W := mkw 0x2c2e1702bb038570 0x0585c2e0576070ae 0x803e1f03e00387f8 0x5007c3e07c0070ff

def z434 : W := mkw 0x9bfde8d9566b5000 0xd37fbd1b2acd6a00 0xffffe0fc1ffff807 0xbffffc1f83ffff00

def z435 : W := mkw 0x0c24140080000000 0x0184828010000000 0x1c381800e0000004 0x038703001c000000

def z436 : W := mkw 0x36c81db43fdf87f0 0x26d903b687fbf0fe 0x7fc01ffc1fff87ff 0xeff803ff83fff0ff

def z437 : W := mkw 0x9e66771e88048c14 0x53cccee3d1009182 0x3c46671c080d9801 0x0788cce38101b300

def z438 : W := mkw 0x12c0089000000000 0x0258011200000000 0x03c000fc00000000 0x8078001f80000000

def z439 : W := mkw 0x164015140d4c0500 0x22c802a281a980a0 0x7fc0071c1ffc0007 0xaff800e383ff8000

def z440 : W := mkw 0x000001240ddcaf9c 0x2000002481bb95f3 0x600000001ffffff8 0x2c00000003ffffff

def z441 : W := mkw 0x0000a04900000000 0x0000140920000000 0x0041e0fc00000000 0x80083c1f80000000

def z442 : W := mkw 0x16c01c9005580180 0x22d8039200ab0030 0x5fc01ffc177001c7 0xcbf803ff82ee0038

def z443 : W := mkw 0x45999df579b667e8 0x28b333beaf36ccfd 0xc3b99ffff0f267fe 0xf87733fffe1e4cff

def z444 : W := mkw 0x9b75400004480000 0x136ea80000890000 0xffffe0001ffc0007 0xbffffc0003ff8000

def z445 : W := mkw 0xbffd5c90f3030160 0x57ffab921e60602c 0x5fb81800f70001c4 0x0bf703001ee00038

def z446 : W := mkw 0x893d400012235000 0x9127a80002446a00 0x0038000000000000 0x0007000000000000

def z447 : W := mkw 0x9ffd5c90177b5180 0xb3ffab9202ef6a30 0x5fb81800177001c4 0x0bf7030002ee0038

def z448 : W := mkw 0x019908a010b24280 0x0033211402164850 0xc3b998e010f267c6 0xf877331c021e4cf8

def z449 : W := mkw 0x4119804170226068 0x082330082e044c0d 0xc3b98003f0f2603e 0xb87730007e1e4c07

def z450 : W := mkw 0x019188e140900280 0x0032311c28120050 0xc3b998e3f0f007c6 0xf877331c7e1e00f8

def z451 : W := mkw 0x0402361a80000000 0x408046c350000000 0x0000071c00000000 0x000000e380000000

def z452 : W := mkw 0x9f7f761a966b5000 0xd3efeec352cd6a00 0xffffe71c1ffff807 0xbffffce383ffff00

def z453 : W := mkw 0x0000000000000000 0x0000000000000000 0x20000000088ff800 0x240000000111ff00

def z454 : W := mkw 0x2c261702a9008570 0x0584c2e0552010ae 0x9c3e1f03e00007ff 0x5387c3e07c0000ff

def z455 : W := mkw 0x4119000070224060 0x082320000e04480c 0x00380000e0000000 0x000700001c000000

def z456 : W := mkw 0x0000804100002008 0x0000100820000401 0x8001800300026038 0x1000300060004c07

def z457 : W := mkw 0x9ff7fefbc0900280 0x53feffdf78120050 0xdffffffff0f007c7 0xfbfffffffe1e00f8

def z458 : W := mkw 0xbb7d41003f6bd570 0x976fa82007ed7aae 0xffffe0001fffffff 0xbffffc0003ffffff

def z459 : W := mkw 0x9b7f43021e6bd410 0x936fe86043cd7a82 0xffffe7031ffffe3f 0xfffffce063ffffc7

def z460 : W := mkw 0x082c000012030000 0x0105800002406000 0xfc7fe0001f8ff807 0xbf8ffc0003f1ff00

def z461 : W := mkw 0x2c2617028b018510 0x0584c2e0516030a2 0x7c061f001f0187c7 0x6f80c3e003e030f8

def z462 : W := mkw 0x9b77e36f0884ae1c 0x136efc6de11095c3 0xbfffe7ff088ffe3f 0xf7fffcffe111ffc7

def z463 : W := mkw 0x0000000000000000 0x0000000000000000 0x8007e0000003f800 0x1000fc0000007f00

def z464 : W := mkw 0x200801243fdf87f0 0x2401002487fbf0fe 0x600000001fff87f8 0x2c00000003fff0ff

def z465 : W := mkw 0x16c01cb000900280 0x02d8039600120050 0x5fc01ffc10f007c7 0xebf803ff821e00f8

def z466 : W := mkw 0x0002020200000000 0x0000404040000000 0x8006070300000003 0x5000c0e060000000

def z467 : W := mkw 0x419988c170226068 0x083331182e044c0d 0x83b998e3e002603e 0xd077331c7c004c07

def z468 : W := mkw 0x2cae1fa2bb9387f0 0x0595c3f4577270fe 0xffbe1fe3fff387ff 0xfff7c3fc7ffe70ff

def z469 : W := mkw 0x240a1702bb038570 0x048142e0576070ae 0x60001f03ff0387f8 0x6c0003e07fe070ff

def z470 : W := mkw 0x9ff7fedbc0000000 0x53feffdb78000000 0x9fbff803e0000004 0x13f7ff007c000000

def z471 : W := mkw 0x419988e170b262e8 0x0833311c2e164c5d 0x43b998e0f0f061c4 0x8877331c1e1e0c38

def z472 : W := mkw 0x2c2e1702bb038570 0x0585c2e0576070ae 0x5c381f03f70007fc 0x4b8703e07ee000ff

def z473 : W := mkw 0x282e0202b2038070 0x0505c0405640700e 0xfc3e0003ff03803f 0x3f87c0007fe07007

def z474 : W := mkw 0x9e66761a80000000 0x53cccec350000000 0x9c7e7f1fe0000007 0x538fcfe3fc000000

def z475 : W := mkw 0x0080088000100080 0x0010011000020010 0x43801800107001c4 0x08700300020e0038

def z476 : W := mkw 0x9a64400006491000 0x934c880000c92200 0x7fc660001ffd9807 0xaff8cc0003ffb300

def z477 : W := mkw 0x57d99cf170b262e8 0x0afb339e2e164c5d 0xdff99ffff0f267ff 0xfbff33fffe1e4cff

def z478 : W := mkw 0x0000010008008410 0x0000002001001082 0x2000000008038638 0x24000000010070c7

def z479 : W := mkw 0x9b7d4000166b5000 0x936fa80002cd6a00 0xffbe00001f738007 0x3ff7c00003ee7000

def z480 : W := mkw 0xdffdddf57fff77e8 0xbbffbbbeafffeefd 0xffffffffffffffff 0xffffffffffffffff

def z481 : W := mkw 0x000801241fff5780 0xa001002483ffeaf0 0x600000001fffffc0 0x2c00000003fffff8

def z482 : W := mkw 0x0002a24b00000000 0x0000544960000000 0x8007e00300000000 0x1000fc0060000000

def z483 : W := mkw 0x0002a36f0884ae1c 0x0000546de11095c3 0x2047e7fc088df801 0x8408fcff8111bf00

def z484 : W := mkw 0x9353e36f0cecfe1c 0x926a7c6de19d9fc3 0xa3c7e7ff08fffe3b 0xf478fcffe11fffc7

def z485 : W := mkw 0x419988e170b262e8 0x0833311c2e164c5d 0x803998e3e00267f8 0x5007331c7c004cff

def z486 : W := mkw 0x24021702a9008570 0x048042e0552010ae 0x7c001f03ff0007ff 0x6f8003e07fe000ff

def z487 : W := mkw 0x4008002036fb72e8 0x8801000406df6e5d 0x600000001ffffff8 0x2c00000003ffffff

def z488 : W := mkw 0xdb7d402036fb72e8 0x9b6fa80406df6e5d 0xffffe0001fffffff 0xbffffc0003ffffff

def z489 : W := mkw 0x12c2abff0cdcae9c 0x2258557fe19b95d3 0xa3c7e7ff08fffe3b 0xf478fcffe11fffc7

def z490 : W := mkw 0x97d15db40dfc5780 0xb2fa2bb681bf8af0 0x7fc1fffc1ffc7fc7 0xeff83fff83ff8ff8

def z491 : W := mkw 0x0482bfffc9940780 0x609057fff93280f0 0x00001fffe00007c0 0x400003fffc0000f8

def z492 : W := mkw 0x0000a0490000280c 0x0000140920000501 0x0001e00000007800 0x00003c0000000f00

def z493 : W := mkw 0xdbfdc8e176fb72e8 0x9b7fb91c2edf6e5d 0xdfb998e3f7f267fe 0xfbf7331c7efe4cff

def z494 : W := mkw 0x0111000000204000 0x0022200000040800 0x0381800000f06000 0x80703000001e0c00

def z495 : W := mkw 0x97d1fdfd4ddc0780 0x72fa3fbfa9bb80f0 0x7fc1fffc1ffc07c7 0xeff83fff83ff80f8

def z496 : W := mkw 0x0002020200008010 0x0000404040001002 0x8006000300038038 0x1000c00060007007

def z497 : W := mkw 0x011ba36f18a6ee1c 0x0023746de314ddc3 0xe3ffe7ff18fffe3f 0xfc7ffcffe31fffc7

def z498 : W := mkw 0x419baaeb70b2eafc 0x0833755d6e165d5f 0xc3bff8e3f0f3fffe 0xf877ff1c7e1e7fff

def z499 : W := mkw 0x9ff7ffdfc8048c14 0x53fefffbf9009182 0xbfffffffe80d9807 0xd7fffffffd01b300

def z500 : W := mkw 0x0002a24b00000000 0x0000544960000000 0x000007ff00000000 0x400000ffe0000000

def z501 : W := mkw 0x0008000010020000 0x0001000002004000 0xc038000010020006 0x3807000002004000

def z502 : W := mkw 0x9e66771e8d4c0500 0x73cccee3d1a980a0 0x3c46671c0f0c0001 0x0788cce381e18000

def z503 : W := mkw 0x000000000000a81c 0x0000000000001503 0x000000000003f838 0x0000000000007f07

def z504 : W := mkw 0x2c24140083010100 0x0584828010602020 0x1c00000007000000 0x0380000000e00000

def z505 : W := mkw 0x0002a34f08048c14 0x00005469e1009182 0xa047e7ff080d9803 0xd408fcffe101b300

def z506 : W := mkw 0x419babef78b6eefc 0x0833757def16dddf 0xc3b99ffff0f267fe 0xf87733fffe1e4cff

def z507 : W := mkw 0x44809df5699427e8 0x289013bead3284fd 0x00001fffe00007f8 0x400003fffc0000ff

def z508 : W := mkw 0x408808a030b262e8 0x0811011406164c5d 0x438018e010f267fe 0xe870031c021e4cff

def z509 : W := mkw 0x04801db409940780 0x209003b6813280f0 0x7c001ffc1f0007c7 0x6f8003ff83e000f8

def z510 : W := mkw 0xdffffedbf03240e0 0x5bffffdb7e06481c 0xdffffffff07001c7 0xdbfffffffe0e0038

def z511 : W := mkw 0x9f7d55001f6b5500 0x93efaaa003ed6aa0 0xffffff001fffffc7 0xffffffe003fffff8

def z512 : W := mkw 0xbf7d5400b76b5160 0x97efaa8016ed6a2c 0x5fb81800f77001c4 0x0bf703001eee0038

def z513 : W := mkw 0x4000002000b06288 0x0800000400160c51 0x0000000000f06000 0x00000000001e0c00

def z514 : W := mkw 0x49bd88e172b362e8 0x0937b11c2e566c5d 0xffbf98e3fff3e7ff 0xfff7f31c7ffe7cff

def z515 : W := mkw 0x2dbf9fc3fb038570 0x05b7f3f87f6070ae 0xffbf9fe3ff0387ff 0xfff7f3fc7fe070ff

def z516 : W := mkw 0x0002a26b00802208 0x0000544d60100441 0x8047e7ff0082663b 0xf008fcffe0104cc7

def z517 : W := mkw 0x2c26370e8b058d14 0x0584c6e1d160b1a2 0x3c46671c0f0d9801 0x0788cce381e1b300

def z518 : W := mkw 0x000a030238028470 0x000140604700508e 0xe03e1f03f80387ff 0x7c07c3e07f0070ff

def z519 : W := mkw 0x3e6617168f4d8510 0x27ccc2e2d1e9b0a2 0x3c46071c0f0d8001 0x0788c0e381e1b000

def z520 : W := mkw 0x619989e17bb3e7f8 0x0c33313c2f767cff 0xe3b998e3fff3e7fe 0xfc77331c7ffe7cff

def z521 : W := mkw 0x200801003b038570 0x04010020076070ae 0xe0381803ff0387fe 0x7c0703007fe070ff

def z522 : W := mkw 0xdffffffffdfe67e8 0x7bffffffffbfccfd 0xfffffffffffe67ff 0xffffffffffffccff

def z523 : W := mkw 0x0824000000000000 0x0104800000000000 0x9c3e000000000007 0x1387c00000000000

def z524 : W := mkw 0x0002a24b0000a81c 0x0000544960001503 0x0000000300000038 0x0000000060000007

def z525 : W := mkw 0x8111400000205000 0x9022280000040a00 0x0001e00000007800 0x00003c0000000f00

def z526 : W := mkw 0x12c009b40ddc0780 0x2258013681bb80f0 0x63c000fc1ffc07c0 0xac78001f83ff80f8

def z527 : W := mkw 0x16c01db40ddc0780 0x22d803b681bb80f0 0x3c401ffc0f0c07c1 0x478803ff81e180f8

def z528 : W := mkw 0x16c01db409940780 0x22d803b6813280f0 0x1fc01ffc000007c7 0xc3f803ff800000f8

def z529 : W := mkw 0x1240000004480000 0x0248000000890000 0x3c4000000f0c0001 0x0788000001e18000

def z530 : W := mkw 0x1240000000000000 0x0248000000000000 0x1fc0000000000007 0x83f8000000000000

def z531 : W := mkw 0x8111e04940000000 0x50223c0928000000 0x0001e00000000000 0x00003c0000000000

def z532 : W := mkw 0x9ff7ffdfcd4c0500 0x73fefffbf9a980a0 0xbfffffffef0c0007 0xd7fffffffde18000

def z533 : W := mkw 0x0000002400840200 0x0000000480108040 0x004000fc008c0000 0x8008001f80118000

def z534 : W := mkw 0x00080000166b5000 0x8001000002cd6a00 0x4000000017700000 0x0800000002ee0000

def z535 : W := mkw 0x419989e578b6eefc 0x0833313caf16dddf 0xe3b998e3f8fffffe 0xfc77331c7f1fffff

def z536 : W := mkw 0x93d148b404fc5280 0xb27a2916809f8a50 0x03c1e0fc00fc7800 0x80783c1f801f8f00

def z537 : W := mkw 0x419988e150b26288 0x0833311c2a164c51 0xc3b980e010f26006 0xb877301c021e4c00

def z538 : W := mkw 0x93d1e8fd44dc0280 0x727a3d1fa89b8050 0x03c1e0fc00fc0000 0x80783c1f801f8000

def z539 : W := mkw 0x9b7d400012030000 0x136fa80002406000 0xffffe0001f038007 0xbffffc0003e07000

def z540 : W := mkw 0x008009a408940680 0x00100134811280d0 0x63c01ffc18fc07c7 0xec7803ff831f80f8

def z541 : W := mkw 0x12c008a004d80280 0x02580114009b0050 0x7fc018e01ffc07c7 0xeff8031c03ff80f8

def z542 : W := mkw 0x0000000005580180 0x2000000000ab0030 0x40000000177001c0 0x0800000002ee0038

def z543 : W := mkw 0x0191088040000000 0x0032211008000000 0x03b81800e0000004 0x007703001c000000

def z544 : W := mkw 0x4082abef6894aefc 0x0810557ded1295df 0xa047ffffe88ffffb 0xf408fffffd11ffff

def z545 : W := mkw 0x9b7fe24b166bf81c 0x936ffc4962cd7f03 0xffffe0031ffff83f 0xbffffc0063ffff07

def z546 : W := mkw 0x9b7d4000166b5000 0x936fa80002cd6a00 0xdfb9800017f26006 0xbbf7300002fe4c00

def z547 : W := mkw 0x3eee1f92bf5b85f0 0x27ddc3f257eb70be 0xffbe1f03ff7387ff 0x7ff7c3e07fee70ff

def z548 : W := mkw 0x0002a36f0884ae1c 0x0000546de11095c3 0xa007e003088ffe38 0x3400fc006111ffc7

def z549 : W := mkw 0x16c01db40ddc0780 0x22d803b681bb80f0 0x3fc007fc0ffc0001 0x87f800ff81ff8000

def z550 : W := mkw 0x8937e24bc000a81c 0x5126fc4978001503 0x803fe003e003f838 0x1007fc007c007f07

def z551 : W := mkw 0x0002a36f0884ae1c 0x0000546de11095c3 0x0041e7ff008c7e38 0xc0083cffe0118fc7

def z552 : W := mkw 0x0000012408840600 0x00000024811080c0 0x20000000088c0600 0x24000000011180c0

def z553 : W := mkw 0x893fe24b1223f81c 0x9127fc4962447f03 0x803fe0030003f838 0x1007fc0060007f07

def z554 : W := mkw 0x0008000030020060 0x000100000600400c 0x40381800f00001c4 0x080703001e000038

def z555 : W := mkw 0x008008b400940280 0x2010011680128050 0x000000fc00000000 0x0000001f80000000

def z556 : W := mkw 0x2c2e1702bf6bd570 0x8585c2e057ed7aae 0xfc3e1f03ffffffff 0x7f87c3e07fffffff

def z557 : W := mkw 0x0000002000800200 0x0000000400100040 0x000000e000800602 0xe000001c001000c0

def z558 : W := mkw 0x6cae9fe3fb93a7f8 0x0d95d3fc7f7274ff 0xfc3e1fe3ff0387ff 0x7f87c3fc7fe070ff

def z559 : W := mkw 0x0002232e0884ae1c 0x00004465c11095c3 0x2046671c088ffe39 0x2408cce38111ffc7

def z560 : W := mkw 0x3eeebfffbfdfaffc 0x27ddd7fff7fbf5ff 0xffffffffffffffff 0xffffffffffffffff

def z561 : W := mkw 0x00080000166b5000 0x8001000002cd6a00 0xe047e0001ffff803 0xbc08fc0003ffff00

def z562 : W := mkw 0x4111804140206008 0x0822300828040c01 0x0001800000006000 0x0000300000000c00

def z563 : W := mkw 0x9ff7fedbc6491000 0xd3feffdb78c92200 0xbfffffffef0d9807 0xd7fffffffde1b300

def z564 : W := mkw 0x2c2e1602b3038170 0x0585c2c05660702e 0xdc3e1803f70381fc 0x1b87c3007ee0703f

def z565 : W := mkw 0x9ff55db4cddc0780 0x73feabb699bb80f0 0x7ff81ffcfffc07c7 0xefff03ff9fff80f8

def z566 : W := mkw 0x200a03023b038570 0x04014060476070ae 0xe00607031f0387fb 0x7c00c0e063e070ff

def z567 : W := mkw 0x93d3ebff4884ae1c 0x527a7d7fe91095c3 0xa3c7e7ff088ffe3b 0xf478fcffe111ffc7

def z568 : W := mkw 0xdffd5c90f03240e0 0x5bffab921e06481c 0x5fb81800f07001c4 0x0bf703001e0e0038

def z569 : W := mkw 0xbfffffdbff6bd570 0xd7fffffb7fed7aae 0xffffffffffffffff 0xffffffffffffffff

def z570 : W := mkw 0x000801241eeffe1c 0x8001002483ddffc3 0x600000001ffffe38 0x2c00000003ffffc7

def z571 : W := mkw 0x0482bedbc0000000 0x409057db78000000 0x8047ffffe0000003 0xd008fffffc000000

def z572 : W := mkw 0x9a6c4000166b5000 0x934d880002cd6a00 0x7c4660001ffff801 0x2f88cc0003ffff00

def z573 : W := mkw 0x0000002400842a0c 0x0000000480108541 0x00000000008c7800 0x0000000000118f00

def z574 : W := mkw 0x40800880601000e0 0x081001100c02001c 0x00001800e00001c0 0x000003001c000038

def z575 : W := mkw 0xbf7f5702bf6bd570 0x97efeae057ed7aae 0xffbe1f03ff7387ff 0x7ff7c3e07fee70ff

def z576 : W := mkw 0x0482bfff0994af9c 0x209057ffe13295f3 0xa047ffff088ffffb 0xf408ffffe111ffff

def z577 : W := mkw 0x16c2bedbc0000000 0x42d857db78000000 0x1fc01fffe0000007 0xc3f803fffc000000

def z578 : W := mkw 0x0000012408840600 0x00000024811080c0 0x000007fc00000600 0x400000ff800000c0

def z579 : W := mkw 0x9b75400000000000 0x136ea80000000000 0xbfffe000088ff807 0xb7fffc000111ff00

def z580 : W := mkw 0x16c2bfff0884ae1c 0x02d857ffe11095c3 0xbfc7ffff088ffe3f 0xf7f8ffffe111ffc7

def z581 : W := mkw 0x419188e1609022e8 0x0832311c2c12045d 0x83b998e3e00007fe 0xd077331c7c0000ff

def z582 : W := mkw 0x0482bfffc884ae1c 0x409057fff91095c3 0x00001fffe0000638 0x400003fffc0000c7

def z583 : W := mkw 0x9bf7eadbc0000000 0x537efd5b78000000 0x83ffe0ffe0000000 0x907ffc1ffc000000

def z584 : W := mkw 0x0002230e08048c14 0x00004461c1009182 0xa046671f080f9e3b 0x7408cce3e101f3c7

def z585 : W := mkw 0x0000a06d00842a0c 0x0000140da0108541 0xa047e0fc088ff803 0xb408fc1f8111ff00

def z586 : W := mkw 0x9b77e24bc0000000 0x536efc4978000000 0x9fffe003e0000007 0x93fffc007c000000

def z587 : W := mkw 0x0000000000000000 0x0000000000000000 0x8001800000826002 0xb000300000104c00

def z588 : W := mkw 0xfffffffbfbb3e7f8 0x5fffffff7f767cff 0xfffffffffff3e7ff 0xfffffffffffe7cff

def z589 : W := mkw 0xbffffedbf2038070 0x57ffffdb7e40700e 0x9fffffffe003803f 0xd3fffffffc007007

def z590 : W := mkw 0x16c01d940d4c0500 0x22d803b281a980a0 0x3fc01ffc0f0c0007 0xc7f803ff81e18000

def z591 : W := mkw 0x282e0202b2038070 0x0505c0405640700e 0xc03e1803f00387fe 0x7807c3007e0070ff

def z592 : W := mkw 0x9ffffedbf0020060 0x53ffffdb7e00400c 0xdffffffff00207ff 0xfbfffffffe0040ff

def z593 : W := mkw 0xd3d9c8e174fa72e8 0x9a7b391c2e9f4e5d 0xc3f9f8e3f0fe7ffe 0xf87f3f1c7e1fcfff

def z594 : W := mkw 0xa93fe24bf2038070 0x5527fc497e40700e 0x803fe003e0038038 0x1007fc007c007007

def z595 : W := mkw 0xbff7ffdbcb018510 0x57fefffb796030a2 0xbfffffffef018007 0xd7fffffffde03000

def z596 : W := mkw 0x200001000b018510 0x04000020016030a2 0x200000000f018000 0x0400000001e03000

def z597 : W := mkw 0x2c2e17029b038510 0x0585c2e0536070a2 0xfc3e07001f038007 0x3f87c0e003e07000

def z598 : W := mkw 0x893fe24bd2235000 0xd127fc497a446a00 0x803fe003e003f800 0x1007fc007c007f00

def z599 : W := mkw 0xdffffefbf6fb72e8 0xdbffffdf7edf6e5d 0xffffffffffffffff 0xffffffffffffffff

def z600 : W := mkw 0x0000000000000000 0x0000000000000000 0x0041e000008c7800 0x80083c0000118f00

def z601 : W := mkw 0x9351400004685000 0x926a2800008d0a00 0xa3c7e00008fff803 0xb478fc00011fff00

def z602 : W := mkw 0x16c2bfff0ddc0780 0x22d857ffe1bb80f0 0xffc7ffff1ffc07c7 0xfff8ffffe3ff80f8

def z603 : W := mkw 0x0400150009000500 0x008002a0012000a0 0x3c0007000f000001 0x078000e001e00000

def z604 : W := mkw 0x3eec1c90b75b01e0 0x27dd839216eb603c 0x5fb81800f77001c4 0x0bf703001eee0038

def z605 : W := mkw 0x89354000c0000000 0x5126a80018000000 0x00380000e0000000 0x000700001c000000

def z606 : W := mkw 0x9b7d4000166b5000 0x936fa80002cd6a00 0x7ffe60001f7d9805 0x0fffcc0003efb300

def z607 : W := mkw 0x9a64400006491000 0x934c880000c92200 0x1c00000007000000 0x0380000000e00000

def z608 : W := mkw 0x000001240884ae1c 0x00000024811095c3 0x0000000000000638 0x00000000000000c7

def z609 : W := mkw 0x57d91c90757a41e0 0x2afb23920eaf483c 0x5fb81800f77001c4 0x0bf703001eee0038

def z610 : W := mkw 0x93594000166b5000 0x926b280002cd6a00 0x63c1e0001ffff800 0xac783c0003ffff00

def z611 : W := mkw 0x124001240ddc0780 0x2248002481bb80f0 0x7fc000001ffc07c7 0xaff8000003ff80f8

def z612 : W := mkw 0x0826020280000000 0x0104c04050000000 0x803e0003e0000000 0x1007c0007c000000

def z613 : W := mkw 0x9240400004481000 0x9248080000890200 0x00406000000c1800 0x00080c0000018300

def z614 : W := mkw 0xdff7fefbc0b06288 0x5bfeffdf78160c51 0x9fffffffe0f06007 0xd3fffffffc1e0c00

def z615 : W := mkw 0x000081650884ae1c 0x0000102ca11095c3 0xa00180e3088ffe3a 0xf400301c6111ffc7

def z616 : W := mkw 0x0002030208008410 0x0000406041001082 0x2006070008018001 0x0400c0e001003000

def z617 : W := mkw 0x3eee1f92bb038570 0x07ddc3f2576070ae 0xfffe1fffff0387ff 0xffffc3ffffe070ff

def z618 : W := mkw 0x2c2e1602b2038070 0x0585c2c05640700e 0x9c3e1f03e003803f 0x5387c3e07c007007

def z619 : W := mkw 0x04801da009900780 0x009003b4013200f0 0x7f801fe01ff007c7 0xeff003fc03fe00f8

def z620 : W := mkw 0x893d4000166b5000 0x9127a80002cd6a00 0xe03fe0001ffff800 0x3c07fc0003ffff00

def z621 : W := mkw 0x0482bfffc884ae1c 0x409057fff91095c3 0xa047ffffe88ffe3b 0xf408fffffd11ffc7

def z622 : W := mkw 0x16c0bdfd0ddc2f8c 0x22d817bfa1bb85f1 0x7fc1fffc1ffc7fc7 0xeff83fff83ff8ff8

def z623 : W := mkw 0x9fffffffdfff5780 0xf3fffffffbffeaf0 0xffffffffffffffc7 0xfffffffffffffff8

def z624 : W := mkw 0x419989e57dfe67e8 0x2833313cafbfccfd 0xe3b998e3fffe67fe 0xfc77331c7fffccff

def z625 : W := mkw 0x12400014044c0000 0x2248000280898000 0x0040001c000c0000 0x0008000380018000

def z626 : W := mkw 0xc9bfeaebf0b262e8 0x5937fd5d7e164c5d 0xc3bff8e3f0f267fe 0xf877ff1c7e1e4cff

def z627 : W := mkw 0x0111000000000000 0x0022200000000000 0x83b9800000000006 0x9077300000000000

def z628 : W := mkw 0xad3ff74bfb038570 0x55a7fee97f6070ae 0xfc3fff03ff0387ff 0x7f87ffe07fe070ff

def z629 : W := mkw 0x13590000146a4000 0x026b2000028d4800 0xfff980001ffe6007 0xbfff300003ffcc00

def z630 : W := mkw 0x0002a36f0ddcaf9c 0x2000546de1bb95f3 0xe047e7ff1ffffffb 0xfc08fcffe3ffffff

def z631 : W := mkw 0x6dbf1f82fb33c5f0 0x0db7e3f05f6678be 0xffbe1f03ff7387ff 0x7ff7c3e07fee70ff

def z632 : W := mkw 0x04801c9000000000 0x0090039200000000 0x00001ffc00000000 0x400003ff80000000

def z633 : W := mkw 0x282ea36fba87ae7c 0x0505d46df750f5cf 0xa07fe7ffe88ffe3b 0xf40ffcfffd11ffc7

def z634 : W := mkw 0x019988c170020060 0x003331182e00400c 0xc3b998e3f00207fe 0xf877331c7e0040ff

def z635 : W := mkw 0x12c008b404dc0280 0x22580116809b8050 0x43c018fc10fc07c6 0xe878031f821f80f8

def z636 : W := mkw 0x57d19df54dfc6788 0x2afa33bea9bf8cf1 0x7fc19ffc1ffc67c7 0xeff833ff83ff8cf8

def z637 : W := mkw 0x419988e170b262e8 0x0833311c2e164c5d 0x438180e010f267f8 0xa870301c021e4cff

def z638 : W := mkw 0xbfff5fb6bfffd7f0 0xb7ffebf6d7fffafe 0xffffffffffffffff 0xffffffffffffffff

def z639 : W := mkw 0x6d3f9743fb23e578 0x0da7f2e87f647caf 0xfc3f9f03ff03e7ff 0x7f87f3e07fe07cff

def z640 : W := mkw 0x4000804160002068 0x080010082c00040d 0x00000003e0000038 0x000000007c000007

def z641 : W := mkw 0x1242a36f0cccae1c 0x0248546de19995c3 0xffc7e7ff1ffffe3f 0xfff8fcffe3ffffc7

def z642 : W := mkw 0x4119002030b262e8 0x0823200406164c5d 0xc3b9800010f267fe 0xb8773000021e4cff

def z643 : W := mkw 0xffffdfe3fffbf7f8 0x9ffffbfc7fff7eff 0xffffffe3ffffffff 0xfffffffc7fffffff

def z644 : W := mkw 0x9b7d41241eef5600 0x936fa82483ddeac0 0xffffe7fc1ffffe07 0xfffffcff83ffffc0

def z645 : W := mkw 0x16c01d900d580580 0x22d803b201ab00b0 0x7f801f001f7007c7 0x6ff003e003ee00f8

def z646 : W := mkw 0x9b75400000000000 0x136ea80000000000 0x1fb8000000000004 0x03f7000000000000

def z647 : W := mkw 0x9b7fe24b166b5000 0x936ffc4962cd6a00 0xffffe7ff1ffff807 0xfffffcffe3ffff00

def z648 : W := mkw 0x2482bfdbe9008570 0x449057fb7d2010ae 0x00001fffe00007f8 0x400003fffc0000ff

def z649 : W := mkw 0x9ffd5c90177b5180 0xb3ffab9202ef6a30 0xfffff8001ffff9c7 0xbfffff0003ffff38

def z650 : W := mkw 0x7fff9ff7ffffe7f8 0x2ffff3fefffffcff 0xffff9fffffffe7ff 0xfffff3fffffffcff

def z651 : W := mkw 0x2c2e1602b3030160 0x0585c2c05660602c 0xdc3e1f03f70001c7 0x5b87c3e07ee00038

def z652 : W := mkw 0x0002220a00000000 0x0000444140000000 0x0046671c00000001 0x0008cce380000000

def z653 : W := mkw 0x2c2e1726bfdf87f0 0x2585c2e4d7fbf0fe 0xfc3e1f03ffff87ff 0x7f87c3e07ffff0ff

def z654 : W := mkw 0x008088e100902288 0x0010111c20120451 0xc38198e310f267fe 0xf870331c621e4cff

def z655 : W := mkw 0x0db79ec3c0000000 0x01b6f3d878000000 0x9fbf9fe3e0000007 0xd3f7f3fc7c000000

def z656 : W := mkw 0x0c2e1602b0020060 0x0185c2c05600400c 0xdc3e1f03f00207ff 0x7b87c3e07e0040ff

def z657 : W := mkw 0x0002a24b00000000 0x0000544960000000 0xa047e7ff088ff803 0xf408fcffe111ff00

def z658 : W := mkw 0x16c01cb404dc0280 0x22d80396809b8050 0x1fc01ffc00fc0007 0xc3f803ff801f8000

def z659 : W := mkw 0x9ff55c90c0000000 0x53feab9218000000 0x9ffff800e0000007 0x93ffff001c000000

def z660 : W := mkw 0x0002a36f0884ae1c 0x0000546de11095c3 0xa00607ff0803863b 0x7400c0ffe10070c7

def z661 : W := mkw 0x9351400004685000 0x926a2800008d0a00 0x0380000000700000 0x00700000000e0000

def z662 : W := mkw 0x9b7d4000166b5000 0x936fa80002cd6a00 0x5ff9e00017fc7804 0x8bff3c0002ff8f00

def z663 : W := mkw 0x600801203bb3e7f8 0x0c01002407767cff 0x600000001ff3e7f8 0x2c00000003fe7cff

def z664 : W := mkw 0xdbfdc8e170b262e8 0x1b7fb91c2e164c5d 0xdffff8e3f0f267ff 0xfbffff1c7e1e4cff

def z665 : W := mkw 0x0008000030020060 0x000100000600400c 0x40000000100207f8 0x28000000020040ff

def z666 : W := mkw 0x019188c140000000 0x0032311828000000 0x038180e000000000 0x8070301c00000000

def z667 : W := mkw 0x9ee45db40fdd1780 0xb3dc8bb681fba2f0 0x7fc67ffc1ffd9fc7 0xeff8cfff83ffb3f8

def z668 : W := mkw 0x0002a36f0884ae1c 0x0000546de11095c3 0x204667ff080d9e39 0x4408ccffe101b3c7

def z669 : W := mkw 0x008088c140000000 0x0010111828000000 0x000018e3e0000000 0x4000031c7c000000

def z670 : W := mkw 0x9ff7ffffcddcaf9c 0x73fefffff9bb95f3 0xffffffffffffffff 0xffffffffffffffff

def z671 : W := mkw 0x4dbf9ee3f0b262e8 0x09b7f3dc7e164c5d 0xdfbf9fe3f0f267ff 0xfbf7f3fc7e1e4cff

def z672 : W := mkw 0x9fffffffdeeffe1c 0xd3fffffffbddffc3 0xfffffffffffffe3f 0xffffffffffffffc7

def z673 : W := mkw 0x2cae1fb6bb9787f0 0x2595c3f6d772f0fe 0xfc3e1fffff0387ff 0x7f87c3ffffe070ff

def z674 : W := mkw 0x4193abef48b4ee9c 0x0832757de9169dd3 0xa3c7e7ff08fffe3b 0xf478fcffe11fffc7

def z675 : W := mkw 0x164015000d480500 0x02c802a001a900a0 0x7fc01f001ffc07c7 0xeff803e003ff80f8

def z676 : W := mkw 0x659b9fe3f9b2e7f8 0x0cb373fc7f365cff 0xc3b99fe3f0f267fe 0xf87733fc7e1e4cff

def z677 : W := mkw 0x0002030208008410 0x0000406041001082 0x0000070300000638 0x400000e0600000c7

def z678 : W := mkw 0x0000806100802208 0x0000100c20100441 0x000180e000806000 0x8000301c00100c00

def z679 : W := mkw 0x2c2e1702bb038570 0x0585c2e0576070ae 0x7c3e1f00ff0181c5 0x0f87c3e01fe03038

def z680 : W := mkw 0x12c0a8fd04dc2a8c 0x2258151fa09b8551 0x03c1e0fc00fc7800 0x80783c1f801f8f00

def z681 : W := mkw 0x6dbd9ce1f3b363e8 0x0db7b39c3e766c7d 0xdfb998e3f7f267fe 0xfbf7331c7efe4cff

def z682 : W := mkw 0x16c01c9005580180 0x22d8039200ab0030 0x7fc018001ffc01c7 0xaff8030003ff8038

def z683 : W := mkw 0x0002a24b0000a81c 0x0000544960001503 0xa047e003088ff83b 0xb408fc006111ff07

def z684 : W := mkw 0x0002a34b08008410 0x0000546961001082 0xa047e7ff0803863b 0xf408fcffe10070c7

def z685 : W := mkw 0x0002220a00008814 0x0000444140001102 0x0006600000019800 0x0000cc0000003300

def z686 : W := mkw 0x9bfd48b416ff5280 0xb37fa91682dfea50 0xffffe0fc1ffff807 0xbffffc1f83ffff00

def z687 : W := mkw 0x3eec1db4bfdf07e0 0x27dd83b697fbe0fc 0x7ff81ffcfffc07c7 0xefff03ff9fff80f8

def z688 : W := mkw 0x24001400a1000160 0x048002801420002c 0x00001800e00001c0 0x000003001c000038

def z689 : W := mkw 0x9ff7fefbc0802208 0x53feffdf78100441 0x9fffffffe082663f 0xf3fffffffc104cc7

def z690 : W := mkw 0x200aa36f3b87af7c 0x0401546de770f5ef 0xe047e7ff1f8ffffb 0xfc08fcffe3f1ffff

def z691 : W := mkw 0x0c26160280000000 0x0184c2c050000000 0x1c06070000000001 0x0380c0e000000000

def z692 : W := mkw 0x1640141005480100 0x22c8028200a90020 0x1c00000007000000 0x0380000000e00000

def z693 : W := mkw 0x0119000010224000 0x0023200002044800 0x43b8000010700004 0x08770000020e0000

def z694 : W := mkw 0x0400151409040500 0x208002a2812080a0 0x0000071c00000000 0x000000e380000000

def z695 : W := mkw 0x893d400012235000 0x9127a80002446a00 0xc3bfe00010f3f806 0xb877fc00021e7f00

def z696 : W := mkw 0x0002a36f0884ae1c 0x0000546de11095c3 0x800187ff0082663a 0xf00030ffe0104cc7

def z697 : W := mkw 0x9a64400006491000 0x934c880000c92200 0xbc47e0000f8ff803 0xb788fc0001f1ff00

def z698 : W := mkw 0x9ffffedbd66b5000 0xd3ffffdb7acd6a00 0xdffffffff7700007 0xdbfffffffeee0000

def z699 : W := mkw 0x9b7d41241eeffe1c 0x936fa82483ddffc3 0xffffe0001ffffe3f 0xbffffc0003ffffc7

def z700 : W := mkw 0xd3d9e8f970b262e8 0x5a7b3d1f2e164c5d 0xc3f9f8fff0f267fe 0xf87f3f1ffe1e4cff

def z701 : W := mkw 0x2c2617028b018510 0x0584c2e0516030a2 0xbc0607030f03863b 0x7780c0e061e070c7

def z702 : W := mkw 0x0000804100000000 0x0000100820000000 0x800180e300000002 0xd000301c60000000

def z703 : W := mkw 0xdbffebef7efffefc 0x9b7ffd7defdfffdf 0xffffffffffffffff 0xffffffffffffffff

def z704 : W := mkw 0x0002a34f0804ac1c 0x00005469e1009583 0xa047e71f080ff839 0x1408fce3e101ff07

def z705 : W := mkw 0xd3d1e8f940b06288 0x5a7a3d1f28160c51 0x03c1e0fc00f06000 0x80783c1f801e0c00

def z706 : W := mkw 0x408888e1709222e8 0x0811111c2e12445d 0xc03818e3f00207fe 0x7807031c7e0040ff

def z707 : W := mkw 0x575995557d6e6568 0x2aeb32aaafadccad 0xbc79871fef0e6039 0x178f30e3fde1cc07

def z708 : W := mkw 0x2c2e1702bb23d570 0x8585c2e057647aae 0xfc3e1f03ff03ffff 0x7f87c3e07fe07fff

def z709 : W := mkw 0x04801db409940780 0x209003b6813280f0 0x7f801ffc1ff007c7 0xeff003ff83fe00f8

def z710 : W := mkw 0xb7535702ad68d570 0x96ea6ae055ad1aae 0x03c1ff03e0fc7ff8 0xc0783fe07c1f8fff

def z711 : W := mkw 0x419b2b8e7836ccf4 0x08336571cf06d99e 0x63fe7f1cf87d99c5 0x0c7fcfe39f0fb338

def z712 : W := mkw 0xd3d1e8f944f87288 0xda7a3d1f289f0e51 0x03c1e0fc00fc7800 0x80783c1f801f8f00

def z713 : W := mkw 0xdae4c8e166d932e8 0x9b5c991c2cdb265d 0x3c4678e3ef0d9ff9 0x4788cf1c7de1b3ff

def z714 : W := mkw 0x16c01db40ddc0780 0x22d803b681bb80f0 0x5fc01ffc17fc07c4 0xcbf803ff82ff80f8

def z715 : W := mkw 0x9ff55db4c884ae1c 0x53feabb6991095c3 0x3fb81800e88ffe3c 0x27f703001d11ffc7

def z716 : W := mkw 0x8dbd5db41bb75780 0xb1b7abb68376eaf0 0x803ffffc0003ffc0 0x5007ffff80007ff8

def z717 : W := mkw 0x05919cd140000000 0x00b2339a28000000 0x83b99fffe0000006 0xd07733fffc000000

def z718 : W := mkw 0x200801243fdfaffc 0x2401002487fbf5ff 0x600000001ffffff8 0x2c00000003ffffff

def z719 : W := mkw 0x2c2cb46db3872b6c 0x0585968db670e56d 0x5c79f8fcf78c79c4 0x8b8f3f1f9ef18f38

def z720 : W := mkw 0x12c009a40cdc0680 0x02580134819b80d0 0x7fc01ffc1ffc07c7 0xeff803ff83ff80f8

def z721 : W := mkw 0x9ff7fedbc4580080 0x73feffdb788b0010 0x9fffffffe0700007 0xd3fffffffc0e0000

def z722 : W := mkw 0x9ff7fedbc4480000 0x53feffdb78890000 0xdffffffff7700007 0xdbfffffffeee0000

def z723 : W := mkw 0x2c2e1702bb038570 0x0585c2e0576070ae 0xfc3e1f03ff8fffff 0x7f87c3e07ff1ffff

def z724 : W := mkw 0xbe6657028f499510 0x97cccae051e932a2 0x3c0607000f018001 0x0780c0e001e03000

def z725 : W := mkw 0x000801243886ae7c 0x000100248710d5cf 0x60000000188ffff8 0x2c0000000311ffff

def z726 : W := mkw 0x0482bedbc0000000 0x409057db78000000 0x80381fffe0000006 0x500703fffc000000

def z727 : W := mkw 0x6db79fe3cbb1e798 0x0db6f3fc79763cf3 0x3f8787e00ff1e001 0x87f0f0fc01fe3c00

def z728 : W := mkw 0x13590000146a4000 0x026b2000028d4800 0xffffe0001ffff807 0xbffffc0003ffff00

def z729 : W := mkw 0x9b7fe36f1eeffe1c 0x936ffc6de3ddffc3 0x5fb807ff1770063c 0x4bf700ffe2ee00c7

def z730 : W := mkw 0x9ff7fedbc4480000 0x53feffdb78890000 0xfffffffffffff807 0xffffffffffffff00

def z731 : W := mkw 0x9ff7fedbc000280c 0x53feffdb78000501 0x9fffffffe0007807 0xd3fffffffc000f00

def z732 : W := mkw 0x164015240dcc0700 0x02c802a481b980e0 0x7fc01ffc1ffc07c7 0xeff803ff83ff80f8

def z733 : W := mkw 0x400801243dfe47e0 0x2801002487bfc8fc 0x600000001ffc07c0 0x2c00000003ff80f8

def z734 : W := mkw 0x200801243b87af7c 0x040100248770f5ef 0x600000001f0387f8 0x2c00000003e070ff

def z735 : W := mkw 0x419988f570b662e8 0x2833311eae16cc5d 0xc3b998fff0f267fe 0xf877331ffe1e4cff

def z736 : W := mkw 0x019988c170224060 0x003331182e04480c 0xc3b998e3f0f267fe 0xf877331c7e1e4cff

def z737 : W := mkw 0x9ff7fedbc0008010 0x53feffdb78001002 0x9fffffffe003803f 0xd3fffffffc007007

def z738 : W := mkw 0x9f77f64b80000000 0x13eefec970000000 0x9fffffffe0000007 0xd3fffffffc000000

def z739 : W := mkw 0x082e03023a038470 0x0105c0604740708e 0xfc3e1f03ff0387ff 0x7f87c3e07fe070ff

def z740 : W := mkw 0x9ff7fedbc0000000 0x53feffdb78000000 0x9fffe7ffe0000001 0x93fffcfffc000000

def z741 : W := mkw 0xb3d9e9d97b038570 0x567b3d3b2f6070ae 0x63c1e0fc1f0387f8 0xac783c1f83e070ff

def z742 : W := mkw 0x419988e570b662e8 0x0833311cae16cc5d 0xc3f998fff0fe67fe 0xf87f331ffe1fccff

def z743 : W := mkw 0x0002032608848610 0x00004064c11090c2 0xa047e7ff088ffe3b 0xf408fcffe111ffc7

def z744 : W := mkw 0x9ff7fedbc000a81c 0x53feffdb78001503 0xbfffffffe88ff83f 0xf7fffffffd11ff07

def z745 : W := mkw 0x419988e170b262e8 0x0833311c2e164c5d 0xc3b998e3f07267fc 0x5877331c7e0e4cff

def z746 : W := mkw 0x8db7fedbc0000000 0x51b6ffdb78000000 0x00381fffe0000000 0x400703fffc000000

def z747 : W := mkw 0xac2e5702bb039570 0x9585cae0576072ae 0xfc3e7f03ff039fff 0x7f87cfe07fe073ff

def z748 : W := mkw 0x9ff7fedbc0000000 0x53feffdb78000000 0xbfffffffe88c0007 0xf7fffffffd118000

def z749 : W := mkw 0x419988e170b262e8 0x0833311c2e164c5d 0xc3b99803f0f267fc 0x387733007e1e4cff

def z750 : W := mkw 0x2c261702ab018570 0x0584c2e0556030ae 0xbc3e1f03ef0187ff 0x5787c3e07de030ff

def z751 : W := mkw 0x4482bfff6994affc 0x289057ffed3295ff 0x00001fffe00007f8 0x400003fffc0000ff

def z752 : W := mkw 0x16c01d900d580580 0x22d803b201ab00b0 0x7fc01ffc1f7007c7 0xeff803ff83ee00f8

def z753 : W := mkw 0x9ff7fedbc0000000 0x53feffdb78000000 0x83ffffffe0000000 0xd07ffffffc000000

def z754 : W := mkw 0x16c01db40ddcaf9c 0x22d803b681bb95f3 0xffc7fffc1fffffff 0xfff8ffff83ffffff

def z755 : W := mkw 0x9ff77e9ac0000000 0x53feefd358000000 0x1ffe7ffce0000007 0xc3ffcfff9c000000

def z756 : W := mkw 0x048abedbd66b5000 0xc09157db7acd6a00 0x60001ffffffff800 0x6c0003ffffffff00

def z757 : W := mkw 0x16c01db40ddc8790 0x22d803b681bb90f2 0x7fc01ffc1fff87ff 0xeff803ff83fff0ff

def z758 : W := mkw 0x200801243fdf07e0 0x2401002487fbe0fc 0x600000001ffc07c0 0x2c00000003ff80f8

def z759 : W := mkw 0x9ee6fedbc0000000 0x53dcdfdb78000000 0x9c7e7fffe0000007 0x538fcffffc000000

def z760 : W := mkw 0x8937e36fcddc0780 0x7126fc6df9bb80f0 0xe03fe003fffc07c0 0x3c07fc007fff80f8

def z761 : W := mkw 0x2c2e370ebb078d74 0x0585c6e1d760f1ae 0xfc7fff1fff8fffff 0xff8fffe3fff1ffff

def z762 : W := mkw 0x419988e570b66aec 0x0833311cae16cd5d 0xc3b998e3f0fe7ffe 0xf877331c7e1fcfff

def z763 : W := mkw 0x8937e36fc884ae1c 0x5126fc6df91095c3 0xa03fe003e88ffe38 0x3407fc007d11ffc7

def z764 : W := mkw 0x2c2e1702bb038570 0x0585c2e0576070ae 0x7c381f03ff0007ff 0x6f8703e07fe000ff

def z765 : W := mkw 0x16c2bedb0558a99c 0x22d857db60ab1533 0xdf87f8031773f9fc 0x1bf0ff0062ee7f3f

def z766 : W := mkw 0x0ca6bedbc0000000 0x4194d7db78000000 0x9c7fffffe0000007 0xd38ffffffc000000

def z767 : W := mkw 0x1ee41c9080000000 0x03dc839210000000 0x1ff81ffce0000007 0xc3ff03ff9c000000

def z768 : W := mkw 0x9ff7fedbc0000000 0x53feffdb78000000 0xbfffffffe80d9807 0xd7fffffffd01b300

def z769 : W := mkw 0x16c01db40ddc8f94 0x22d803b681bb91f2 0x7fc01ffc1ffd9fc7 0xeff803ff83ffb3f8

def z770 : W := mkw 0x419988e170b262e8 0x0833311c2e164c5d 0xffb998e3fff267ff 0xfff7331c7ffe4cff

def z771 : W := mkw 0x240a1702b9028570 0x048142e0572050ae 0xfc381f03ff0207ff 0x7f8703e07fe040ff

def z772 : W := mkw 0x16c01db40ddc0780 0x22d803b681bb80f0 0x7fc007fc1ffc07c1 0xaff800ff83ff80f8

def z773 : W := mkw 0x419988e170b262e8 0x0833311c2e164c5d 0xc3f9f8e3f0fe7ffe 0xf87f3f1c7e1fcfff

def z774 : W := mkw 0x16c01db40ddc0780 0x22d803b681bb80f0 0xfff81ffffffc07c7 0xffff03ffffff80f8

def z775 : W := mkw 0x53d1a8fd44fc6a8c 0x2a7a351fa89f8d51 0x03c1e0fc00fc7800 0x80783c1f801f8f00

def z776 : W := mkw 0xbe66771e8f4d8510 0x77cccee3d1e9b0a2 0x3c46671c0f0d8001 0x0788cce381e1b000

def z777 : W := mkw 0x0ca6bedbc0000000 0x4194d7db78000000 0x803e1fffe0000000 0x5007c3fffc000000

def z778 : W := mkw 0x2c2e1702bb038570 0x0585c2e0576070ae 0xbc3e1f03ef0387f9 0x5787c3e07de070ff

def z779 : W := mkw 0x000001240884ae1c 0x00000024811095c3 0xa047e7fc088ffe3b 0xf408fcff8111ffc7

def z780 : W := mkw 0x2c261702a9008570 0x0584c2e0552010ae 0xfc3e1f03ff0007ff 0x7f87c3e07fe000ff

def z781 : W := mkw 0x96c05db40ddc1780 0xb2d80bb681bb82f0 0x7fc07ffc1ffc1fc7 0xeff80fff83ff83f8

def z782 : W := mkw 0x9a64400006491000 0x934c880000c92200 0xffc7e0001ffff807 0xbff8fc0003ffff00

def z783 : W := mkw 0x53d188f144f86288 0x2a7a311e289f0c51 0x038180e000f06000 0x8070301c001e0c00

def z784 : W := mkw 0x419188e160b062e8 0x0832311c2c160c5d 0x83b998e3e0f067fe 0xd077331c7c1e0cff

def z785 : W := mkw 0x2c2c1400b3030160 0x058582801660602c 0x5c381803f70007fc 0x4b8703007ee000ff

def z786 : W := mkw 0xde6e763ab0b262e8 0x5bcdcec756164c5d 0x5c46671c10f267f9 0x2b88cce3821e4cff

def z787 : W := mkw 0x3aee0ab6b6df82f0 0x275dc156d6dbf05e 0x83fe00ffe0ff8038 0x907fc01ffc1ff007

def z788 : W := mkw 0xc199c8e170b272e8 0x9833391c2e164e5d 0xc3b9f8e3f0f27ffe 0xf8773f1c7e1e4fff

def z789 : W := mkw 0xd3d1c8f544fc7288 0xba7a391ea89f8e51 0x03c1e0fc00fc7800 0x80783c1f801f8f00

def z790 : W := mkw 0x2c2e1702bb038570 0x0585c2e0576070ae 0xdc3e1f03f70007ff 0x5b87c3e07ee000ff

def z791 : W := mkw 0x16c01d940d5c0580 0x22d803b281ab80b0 0x7fc01ffc1f7c01c7 0xcff803ff83ef8038

def z792 : W := mkw 0x0002a36f0884ae1c 0x0000546de11095c3 0xfc47e7ff1f8ffe3f 0xff88fcffe3f1ffc7

def z793 : W := mkw 0x0002a24b00000000 0x0000544960000000 0x807fffffe0000007 0xd00ffffffc000000

def z794 : W := mkw 0x400801243dfeeffc 0x2801002487bfddff 0x600000001ffffff8 0x2c00000003ffffff

def z795 : W := mkw 0x0482bfffc994af9c 0x609057fff93295f3 0x00001fffe00007f8 0x400003fffc0000ff

def z796 : W := mkw 0x0ca6bedbc0000000 0x4194d7db78000000 0x1c381fffe0000004 0x438703fffc000000

def z797 : W := mkw 0x2c2e370abb038570 0x0585c6e1576070ae 0xfc7e7f1fff0387ff 0x7f8fcfe3ffe070ff

def z798 : W := mkw 0xbffd5c90f76b5160 0xd7ffab921eed6a2c 0x5fb81800f77001c4 0x0bf703001eee0038

def z799 : W := mkw 0x4199a8f970b262e8 0x4833351f2e164c5d 0xc3b998fff0f267fe 0xf877331ffe1e4cff

def z800 : W := mkw 0x9e66f65b80000000 0x53ccdecb70000000 0x9c7fffffe0000007 0xd38ffffffc000000

def z801 : W := mkw 0x1ee6bedbc0000000 0x43dcd7db78000000 0x9ffe1fffe0000007 0xd3ffc3fffc000000

def z802 : W := mkw 0x0002a26b00802208 0x0000544d60100441 0xa047e7ff088ffe3b 0xf408fcffe111ffc7

def z803 : W := mkw 0x2c2e1706bb078570 0x0585c2e0d760f0ae 0xfc7e1f1fff0f87ff 0x7f8fc3e3ffe1f0ff

def z804 : W := mkw 0x9ff7fedbc0000000 0x53feffdb78000000 0x1ff9ffffe0000004 0xc3ff3ffffc000000

def z805 : W := mkw 0x17d11c9040000000 0x02fa239208000000 0x1ff81ffce0000007 0xc3ff03ff9c000000

def z806 : W := mkw 0x8db7fedbc0000000 0x51b6ffdb78000000 0x83bfffffe0000006 0xd077fffffc000000

def z807 : W := mkw 0x019188c140000000 0x0032311828000000 0x83f99fffe0000007 0xd07f33fffc000000

def z808 : W := mkw 0x419988e170b262e8 0x0833311c2e164c5d 0x43b818e3f0f007fe 0xe877031c7e1e00ff

def z809 : W := mkw 0x9ff7fedbc0000000 0x53feffdb78000000 0x9fbe1fffe0000007 0x53f7c3fffc000000

def z810 : W := mkw 0x0002a36f0884ae1c 0x0000546de11095c3 0xa047e7ff080ffe39 0x5408fcffe101ffc7

def z811 : W := mkw 0x16c01d900d480500 0x02d803b201a900a0 0x7fc01ffc1ffc07c7 0xeff803ff83ff80f8

def z812 : W := mkw 0x124001240ddc0780 0x2248002481bb80f0 0x7fc007fc1ffc07c7 0xeff800ff83ff80f8

def z813 : W := mkw 0x0002a36f0884ae1c 0x0000546de11095c3 0x8047e7ff008ffe38 0xd008fcffe011ffc7

def z814 : W := mkw 0x2482bfffa994affc 0x249057fff53295ff 0x00001fffe00007f8 0x400003fffc0000ff

def z815 : W := mkw 0x9b7d4000166b5000 0x936fa80002cd6a00 0xffffe0031ffffe3f 0xfffffc0063ffffc7

def z816 : W := mkw 0x9ff7fedbc4480000 0x53feffdb78890000 0xbfffffffef0c0007 0xd7fffffffde18000

def z817 : W := mkw 0x9ff7fedbc6695000 0xd3feffdb78cd2a00 0xbfffffffeffdf807 0xd7fffffffdffbf00

def z818 : W := mkw 0x040a170239028570 0x008142e0472050ae 0xfc3e1f03ff0387ff 0x7f87c3e07fe070ff

def z819 : W := mkw 0x9ff75e9280000000 0x13feebd250000000 0x9fffffffe0000007 0xd3fffffffc000000

def z820 : W := mkw 0x9ff7fedbc0000000 0x53feffdb78000000 0x1ffffffce0000005 0x83ffffff9c000000

def z821 : W := mkw 0x9f77f65bc0000000 0x53eefecb78000000 0x9c7fe7ffe0000003 0xd38ffcfffc000000

def z822 : W := mkw 0x600801243bb7effc 0x0c0100248776fdff 0x600000001ffffff8 0x2c00000003ffffff

def z823 : W := mkw 0x9ff7fedbc4685000 0xd3feffdb788d0a00 0x9fffffffe0700007 0xd3fffffffc0e0000

def z824 : W := mkw 0x019908a030b242e0 0x003321140616485c 0xc3b998e3f0f267fe 0xf877331c7e1e4cff

def z825 : W := mkw 0x9ff7fedbc4685000 0xd3feffdb788d0a00 0xfffffffffffc7807 0xffffffffffff8f00

def z826 : W := mkw 0x2c2e1702bb038570 0x0585c2e0576070ae 0xffbe1f03fff387ff 0xfff7c3e07ffe70ff

def z827 : W := mkw 0x400801243fff77e8 0xa801002487ffeefd 0x600000001ffffff8 0x2c00000003ffffff

def z828 : W := mkw 0x0c26160280000000 0x0184c2c050000000 0x9c7e1fffe0000007 0xd38fc3fffc000000

def z829 : W := mkw 0x2c2e1702bb038570 0x0585c2e0576070ae 0xfc7e1fffff0387ff 0xff8fc3ffffe070ff

def z830 : W := mkw 0x9ff5dcd1c0000000 0x53febb9a38000000 0x9ff99fffe0000007 0xd3ff33fffc000000

def z831 : W := mkw 0x9ff7fedbc4685000 0xd3feffdb788d0a00 0xbfffffffe8fff807 0xf7fffffffd1fff00

def z832 : W := mkw 0x9351400004685000 0x926a2800008d0a00 0xffc7e0001ffff807 0xbff8fc0003ffff00

def z833 : W := mkw 0x082c000032030060 0x010580000640600c 0xdc381803f70207fe 0x7b8703007ee040ff

def z834 : W := mkw 0xbe66771a8f499510 0xd7cccee351e932a2 0x3c46671c0f0d9801 0x0788cce381e1b300

def z835 : W := mkw 0xdffd5c90f67b50e0 0xdbffab921ecf6a1c 0x5fb81800f77001c4 0x0bf703001eee0038

def z836 : W := mkw 0x9ff55c90c0000000 0x53feab9218000000 0x9ffffffce0000007 0xd3ffffff9c000000

def z837 : W := mkw 0x9ff7fedbc4481000 0xd3feffdb78890200 0x9fffffffe00c1807 0xd3fffffffc018300

def z838 : W := mkw 0x00880880301200e0 0x001101100602401c 0xc3b81803f07207fe 0x787703007e0e40ff

def z839 : W := mkw 0xc93fe24b7223f87c 0x9927fc496e447f0f 0x803fe003e003f838 0x1007fc007c007f07

def z840 : W := mkw 0x0002a36f0894ae9c 0x0000546de11295d3 0xe047e7ff18fffffb 0xfc08fcffe31fffff

def z841 : W := mkw 0xdb7d4000766b5060 0x9b6fa8000ecd6a0c 0xffffe000fffff807 0xbffffc001fffff00

def z842 : W := mkw 0x93d3eadb40000000 0x527a7d5b68000000 0x83ffffffe0000007 0xd07ffffffc000000

def z843 : W := mkw 0x0593bedbc0000000 0x40b277db78000000 0x83ffffffe0000007 0xd07ffffffc000000

def z844 : W := mkw 0x9ff7fedbc0000000 0x53feffdb78000000 0xffffffffff000007 0xffffffffffe00000

def z845 : W := mkw 0x9ee67e9a80000000 0x53dccfd350000000 0x9ffe7fffe0000007 0xd3ffcffffc000000

def z846 : W := mkw 0x0008000030020060 0x000100000600400c 0xfc381803ff0207ff 0x7f8703007fe040ff

def z847 : W := mkw 0x89b7eacbc0000000 0x5136fd5978000000 0x83ffffffe0000007 0xd07ffffffc000000

def z848 : W := mkw 0x1ee6bedb80000000 0x03dcd7db70000000 0x9fffffffe0000007 0xd3fffffffc000000

def z849 : W := mkw 0x9ff7fedbc0000000 0x53feffdb78000000 0xbfffffffe8038007 0xf7fffffffd007000

def z850 : W := mkw 0x2c2c1500bb030560 0x058582a0176060ac 0xfc381f03ff0207ff 0x7f8703e07fe040ff

def z851 : W := mkw 0x2c2e1702bb038570 0x0585c2e0576070ae 0x7c3e1f03ff0187fd 0x4f87c3e07fe030ff

def z852 : W := mkw 0xa93fe24bf223d070 0xd527fc497e447a0e 0x803fe003e003f838 0x1007fc007c007f07

def z853 : W := mkw 0x16c01c9005580180 0x22d8039200ab0030 0x5f801ffc177001c4 0x4bf003ff82ee0038

def z854 : W := mkw 0x16c01db40ddc0780 0x22d803b681bb80f0 0xffc01fff1ffe07ff 0xfff803ffe3ffc0ff

def z855 : W := mkw 0x0593bedbc0000000 0x40b277db78000000 0x80399fffe0000000 0x500733fffc000000

def z856 : W := mkw 0x2c2e1702bb038570 0x0585c2e0576070ae 0xfc3e1803ff0387fc 0x3f87c3007fe070ff

def z857 : W := mkw 0x419988e170b262e8 0x0833311c2e164c5d 0xc3f99ffff0f267ff 0xf87f33fffe1e4cff

def z858 : W := mkw 0x9b77e24bc0000000 0x536efc4978000000 0x9fffe7ffe0000007 0xd3fffcfffc000000

def z859 : W := mkw 0x2c2e1702bb23c570 0x0585c2e0576478ae 0xfc3e1f03fff3e7ff 0x7f87c3e07ffe7cff

def z860 : W := mkw 0x9ff7fedbc0000000 0x53feffdb78000000 0x9fbfffffe0000004 0x53f7fffffc000000

def z861 : W := mkw 0x9ff7fedbc0000000 0x53feffdb78000000 0x1ffe7fffe0000005 0x43ffcffffc000000

def z862 : W := mkw 0x2c2e1702bb038570 0x0585c2e0576070ae 0xfc7fff03ff0387ff 0xff8fffe07fe070ff

def z863 : W := mkw 0x9ff7fedbc1000100 0x53feffdb78200020 0xdffffffff70001c7 0xdbfffffffee00038

def z864 : W := mkw 0x9ff7fedbc1100180 0x73feffdb78220030 0x9fffffffe00001c7 0xd3fffffffc000038

def z865 : W := mkw 0x0c2e1702b9020560 0x0185c2e0572040ac 0xfc3e1f03ff0207ff 0x7f87c3e07fe040ff

def z866 : W := mkw 0x16c01db40ddc2788 0x22d803b681bb84f1 0x7fc01ffc1ffe67ff 0xeff803ff83ffccff

def z867 : W := mkw 0x0593bedbc0000000 0x40b277db78000000 0x03b81fffe0000004 0x407703fffc000000

def z868 : W := mkw 0x9ff7fedbc5580180 0x73feffdb78ab0030 0xfffffffffffc01c7 0xffffffffffff8038

def z869 : W := mkw 0x0002a36f0884ae1c 0x0000546de11095c3 0xe047ffff188fffff 0xfc08ffffe311ffff

def z870 : W := mkw 0xbff7fedbc2018010 0x57feffdb78403002 0x9fffffffe0018007 0xd3fffffffc003000

def z871 : W := mkw 0x0002a34f0804ac1c 0x00005469e1009583 0xa047e7ff080ff83b 0xd408fcffe101ff07

def z872 : W := mkw 0x0193aacb40000000 0x0032755968000000 0x83b99fffe0000006 0xd07733fffc000000

def z873 : W := mkw 0x3e66371e8f4d8d14 0x27ccc6e3d1e9b1a2 0x3c46671c0f0d9801 0x0788cce381e1b300

def z874 : W := mkw 0x16c01db40ddc0780 0x22d803b681bb80f0 0x7fc67ffc1ffd9fc7 0xeff8cfff83ffb3f8

def z875 : W := mkw 0x2c2e1702bb038570 0x0585c2e0576070ae 0xfc3fff03ff03ffff 0x7f87ffe07fe07fff

def z876 : W := mkw 0x419988e170b262e8 0x0833311c2e164c5d 0xe3b998e3f8fffffe 0xfc77331c7f1fffff

def z877 : W := mkw 0x408888e1709222e8 0x0811111c2e12445d 0xc3b818e3f0f207fe 0xf877031c7e1e40ff

def z878 : W := mkw 0x419988e170b262e8 0x0833311c2e164c5d 0xe3bf98e3f8f3e7ff 0xfc77f31c7f1e7cff

def z879 : W := mkw 0x16c01db40ddc0780 0x22d803b681bb80f0 0x5fc01ffc177007c7 0xcbf803ff82ee00f8

def z880 : W := mkw 0xdff7fedbc0206008 0x5bfeffdb78040c01 0x9fffffffe0006007 0xd3fffffffc000c00

def z881 : W := mkw 0x9b7d4000366b5060 0x936fa80006cd6a0c 0xfffff800fffff9c7 0xbfffff001fffff38

def z882 : W := mkw 0x400801243efffefc 0x8801002487dfffdf 0x600000001ffffff8 0x2c00000003ffffff

def z883 : W := mkw 0x9b7d4000366b5060 0x936fa80006cd6a0c 0xffffe003fffff83f 0xbffffc007fffff07

def z884 : W := mkw 0x16c01db40ddc0780 0x22d803b681bb80f0 0x7fc01ffc1ffc01c5 0x8ff803ff83ff8038

def z885 : W := mkw 0x693fa24bf223e87c 0x0d27f4497e447d0f 0x803fe003e003f838 0x1007fc007c007f07

def z886 : W := mkw 0x9ff7fedbc0000000 0x53feffdb78000000 0x9fffffffe0826007 0xf3fffffffc104c00

def z887 : W := mkw 0x2c2e1602b3030160 0x0585c2c05660602c 0xdc3e1f03f70207ff 0x7b87c3e07ee040ff

def z888 : W := mkw 0x9ff7fedbc6491000 0xd3feffdb78c92200 0xbfffffffef8ff807 0xf7fffffffdf1ff00

def z889 : W := mkw 0x200801243b9787f0 0x240100248772f0fe 0x600000001f0387f8 0x2c00000003e070ff

def z890 : W := mkw 0x282c01003b038570 0x05058020076070ae 0xfc3e1803ff0387ff 0x7f87c3007fe070ff

def z891 : W := mkw 0x419908a070b262e8 0x083321140e164c5d 0xc3b81803f0f267fe 0x787703007e1e4cff

def z892 : W := mkw 0x2c2e1702bb038570 0x0585c2e0576070ae 0xfc3f9f03ff83e7ff 0xff87f3e07ff07cff

def z893 : W := mkw 0x16c01db4cddc0780 0x62d803b699bb80f0 0x7fc01ffcfffc07c7 0xeff803ff9fff80f8

def z894 : W := mkw 0x019188e140902288 0x0032311c28120451 0xc3b998e3f0f267fe 0xf877331c7e1e4cff

def z895 : W := mkw 0x2c2c1400b3030160 0x058582801660602c 0xfc3e1803ff0387ff 0x7f87c3007fe070ff

def z896 : W := mkw 0x000801243dde07e0 0x2001002487bbc0fc 0x600000001ffe07f8 0x2c00000003ffc0ff

def z897 : W := mkw 0x419988e170b262e8 0x0833311c2e164c5d 0xc3bff8e3f0f3fffe 0xf877ff1c7e1e7fff

def z898 : W := mkw 0x41990880703240e0 0x083321100e06481c 0xc3b99803f0f267fe 0xf87733007e1e4cff

def z899 : W := mkw 0x4199a8e970b262e8 0x0833351d2e164c5d 0xc3f9f8fff0f267fe 0xf87f3f1ffe1e4cff

def z900 : W := mkw 0x419988c1703240e0 0x083331182e06481c 0xc3b998e3f07207fe 0xf877331c7e0e40ff

def z901 : W := mkw 0xbe6657168f4d9510 0xb7cccae2d1e9b2a2 0x3c46671c0f0d9801 0x0788cce381e1b300

def z902 : W := mkw 0xbff7fedbc3010100 0x57feffdb78602020 0x9fffffffe7000007 0xd3fffffffce00000

def z903 : W := mkw 0x0ca61e9280000000 0x0194c3d250000000 0x9c3e1fffe0000007 0x5387c3fffc000000

def z904 : W := mkw 0x93d1e8fd44dc2a8c 0x727a3d1fa89b8551 0x03c1e0fc00fc7800 0x80783c1f801f8f00

def z905 : W := mkw 0x9ff7fedbc0000000 0x53feffdb78000000 0x9fffffffe003f807 0xd3fffffffc007f00

def z906 : W := mkw 0x0408140031020160 0x008102800620402c 0xdc381803f70207fe 0x7b8703007ee040ff

def z907 : W := mkw 0x16c01cb005d80380 0x22d8039600bb0070 0x5fc01ffc17f007c7 0xebf803ff82fe00f8

def z908 : W := mkw 0x1ff79ed3c0000000 0x03fef3da78000000 0x9fff9fffe0000007 0xd3fff3fffc000000

def z909 : W := mkw 0xe93fe24bf223e078 0x5d27fc497e447c0f 0x803fe003e003e038 0x1007fc007c007c07

def z910 : W := mkw 0x2c2e370abb038d74 0x0585c6e1576071ae 0xfc3e7f03ff039fff 0x7f87cfe07fe073ff

def z911 : W := mkw 0x4008012439b667e8 0x280100248736ccfd 0x4000000010f267f8 0x28000000021e4cff

def z912 : W := mkw 0x16c01db40ddc0780 0x22d803b681bb80f0 0xffc61ffc1fff87c7 0xfff8c3ff83fff0f8

def z913 : W := mkw 0x2c2e1706bb078d74 0x0585c2e0d760f1ae 0xfc3e1f03ff0f9fff 0x7f87c3e07fe1f3ff

def z914 : W := mkw 0x9b7d4000166b5000 0x936fa80002cd6a00 0xfffff803fffff807 0xffffff007fffff00

def z915 : W := mkw 0x4199a8e970b26aec 0x0833351d2e164d5d 0xc3b9f8e3f0f27ffe 0xf8773f1c7e1e4fff

def z916 : W := mkw 0x0c2c15003b030560 0x018582a0076060ac 0xfc3e1f03ff0387ff 0x7f87c3e07fe070ff

def z917 : W := mkw 0x9ff7fedbc0000000 0x53feffdb78000000 0x1ff81fffe0000007 0xc3ff03fffc000000

def z918 : W := mkw 0x9ff7fedbc0000000 0x53feffdb78000000 0x9fb99fffe0000006 0xd3f733fffc000000

def z919 : W := mkw 0x8937e24bc0000000 0x5126fc4978000000 0x803fe7ffe0000000 0x5007fcfffc000000

def z920 : W := mkw 0x9ff7fedbc000a81c 0x53feffdb78001503 0x9fffffffe000003f 0xd3fffffffc000007

def z921 : W := mkw 0x0119806130a26268 0x0023300c26144c4d 0xc3b998e3f0f267fe 0xf877331c7e1e4cff

def z922 : W := mkw 0x0002a36fc884ae1c 0x4000546df91095c3 0xa047e7ffe88ffe3b 0xf408fcfffd11ffc7

def z923 : W := mkw 0x2c2e1602b3038170 0x0585c2c05660702e 0xdc3e1803f70387fe 0x7b87c3007ee070ff

def z924 : W := mkw 0xa93fe24bb223f87c 0x9527fc4976447f0f 0x803fe003e003f838 0x1007fc007c007f07

def z925 : W := mkw 0xbb7d4000b66b5060 0x976fa80016cd6a0c 0xffffe000fffff807 0xbffffc001fffff00

def z926 : W := mkw 0x8d37f64bc0000000 0x51a6fec978000000 0x9c7fffffe0000007 0xd38ffffffc000000

def z927 : W := mkw 0x9ff7fedbc0100080 0x53feffdb78020010 0xdffffffff07001c7 0xdbfffffffe0e0038

def z928 : W := mkw 0x8db7fedbc0000000 0x51b6ffdb78000000 0x807fffffe0000003 0xd00ffffffc000000

def z929 : W := mkw 0x2c2e1702bb038570 0x0585c2e0576070ae 0x7c381f03ff0387fc 0x6f8703e07fe070ff

def z930 : W := mkw 0x419908a070b242e0 0x083321140e16485c 0xc3b818e3f0f207fe 0xf877031c7e1e40ff

def z931 : W := mkw 0x419988e170b262e8 0x0833311c2e164c5d 0xe3f998e3f8fe67ff 0xfc7f331c7f1fccff

def z932 : W := mkw 0x0002a26f0084aa1c 0x0000544de0109543 0x8047e7ff008ff83b 0xd008fcffe011ff07

def z933 : W := mkw 0x16c01cb405dc0380 0x22d8039680bb8070 0x5fc01ffc17fc01c7 0xcbf803ff82ff8038

def z934 : W := mkw 0x9b75400006695000 0x936ea80000cd2a00 0xbfc7e0000ffff803 0xb7f8fc0001ffff00

def z935 : W := mkw 0xdffd5c90777b51e0 0xbbffab920eef6a3c 0x5fb81800f77001c4 0x0bf703001eee0038

def z936 : W := mkw 0x419188e1609022e8 0x0832311c2c12045d 0xc3b998e3f0f007fe 0xf877331c7e1e00ff

def z937 : W := mkw 0x9b7d4000366b5060 0x936fa80006cd6a0c 0xffffe0001fffffff 0xbffffc0003ffffff

def z938 : W := mkw 0x4119002030b262e8 0x0823200406164c5d 0xc3b99803f0f267fe 0xf87733007e1e4cff

def z939 : W := mkw 0x16c01db40ddc0780 0x22d803b681bb80f0 0x7f801ffc1f7007c7 0x6ff003ff83ee00f8

def z940 : W := mkw 0xd3d1e8ed44fc7a8c 0x9a7a3d1da89f8f51 0x03c1e0fc00fc7800 0x80783c1f801f8f00

def z941 : W := mkw 0x408808a030b262e8 0x0811011406164c5d 0xc3b818e3f0f267fe 0xf877031c7e1e4cff

def z942 : W := mkw 0x419988e170b262e8 0x0833311c2e164c5d 0x43b818e3f0f267fc 0x6877031c7e1e4cff

def z943 : W := mkw 0x9ff5dcd140000000 0x13febb9a28000000 0x9fffffffe0000007 0xd3fffffffc000000

def z944 : W := mkw 0x0113a24b40000000 0x0022744968000000 0x807fe7ffe0000003 0xd00ffcfffc000000

def z945 : W := mkw 0x093d000012234000 0x0127a00002446800 0xffffe0001ffff807 0xbffffc0003ffff00

def z946 : W := mkw 0x2c2e1702bb038570 0x0585c2e0576070ae 0xdc3e1f03f70387fc 0x5b87c3e07ee070ff

def z947 : W := mkw 0x9b75400004480000 0x136ea80000890000 0xffffe0001ffff807 0xbffffc0003ffff00

def z948 : W := mkw 0x0c26b64b80000000 0x0184d6c970000000 0x9c3e1fffe0000007 0x5387c3fffc000000

def z949 : W := mkw 0x16c01db40ddc0780 0x22d803b681bb80f0 0xffc7fffc1ffc07c7 0xfff8ffff83ff80f8

def z950 : W := mkw 0x200801243fffd7f0 0xa401002487fffafe 0x600000001ffffff8 0x2c00000003ffffff

def z951 : W := mkw 0x53d188e144f86288 0x0a7a311c289f0c51 0x03c180e000fc6000 0x8078301c001f8c00

def z952 : W := mkw 0x9ff55c90c0000000 0x53feab9218000000 0x1fb81ffce0000004 0x43f703ff9c000000

def z953 : W := mkw 0x419988e170b262e8 0x0833311c2e164c5d 0xc3b998e3f07007fe 0xd877331c7e0e00ff

def z954 : W := mkw 0x019988e1709202e0 0x0033311c2e12405c 0xc3b998e3f0f207fe 0xf877331c7e1e40ff

def z955 : W := mkw 0x419988e170b262e8 0x0833311c2e164c5d 0xc3fff8e3f0f267ff 0xf87fff1c7e1e4cff

def z956 : W := mkw 0x282e0202b2038070 0x0505c0405640700e 0xfc3e1803ff0387ff 0x7f87c3007fe070ff

def z957 : W := mkw 0x4008012438a6ee7c 0x080100248714ddcf 0x20000000088ffe38 0x240000000111ffc7

def z958 : W := mkw 0x9e66771e8d4c8d14 0x73cccee3d1a991a2 0x3c46671c0f0d9801 0x0788cce381e1b300

def z959 : W := mkw 0x9ff7fedbc0000000 0x53feffdb78000000 0x9fffffffe002063f 0xf3fffffffc0040c7

def z960 : W := mkw 0x4119804170226068 0x082330082e044c0d 0xc3b99803f0f267fe 0xf87733007e1e4cff

def z961 : W := mkw 0x17d3bedbc0000000 0x42fa77db78000000 0x9ff99fffe0000007 0xd3ff33fffc000000

def z962 : W := mkw 0x9b75400006695000 0x936ea80000cd2a00 0xbfffe0000ffdf807 0x97fffc0001ffbf00

def z963 : W := mkw 0x41990880703240e0 0x083321100e06481c 0x43b81803f07007fc 0x487703007e0e00ff

def z964 : W := mkw 0x9ff7fedbc0008814 0x53feffdb78001102 0x9fffffffe0019807 0xd3fffffffc003300

def z965 : W := mkw 0x4008012438b6eefc 0x080100248716dddf 0x4000000010f267f8 0x28000000021e4cff

def z966 : W := mkw 0x9b75400006695000 0x936ea80000cd2a00 0x7fc7e0001ffdf807 0xaff8fc0003ffbf00

def z967 : W := mkw 0x200801243b878770 0x040100248770f0ee 0x600000001f8f87f8 0x2c00000003f1f0ff

def z968 : W := mkw 0x1a6c0000164b0000 0x034d800002c96000 0xffffe0001ffff807 0xbffffc0003ffff00

def z969 : W := mkw 0x200801243fefff7c 0x8401002487fdffef 0x600000001ffffff8 0x2c00000003ffffff

def z970 : W := mkw 0x16c01db40ddc0780 0x22d803b681bb80f0 0x7fc01ffc1fffffc7 0xeff803ff83fffff8

def z971 : W := mkw 0x9ff55db4cddc0780 0x73feabb699bb80f0 0x7fb81800fffc07c4 0x2ff703001fff80f8

def z972 : W := mkw 0x4008012438b666e8 0x080100248716ccdd 0x6000000018fe67f8 0x2c000000031fccff

def z973 : W := mkw 0xd3d1c8e144f87288 0x9a7a391c289f0e51 0x038180e000f06000 0x8070301c001e0c00

def z974 : W := mkw 0x9b7d4000166b5000 0x936fa80002cd6a00 0xfffff8001fffffc7 0xffffff0003fffff8

def z975 : W := mkw 0x2c2e371abb038570 0x4585c6e3576070ae 0xfc3e1f1fff0387ff 0x7f87c3e3ffe070ff

def z976 : W := mkw 0x16c01db40ddc0780 0x22d803b681bb80f0 0x7f801ffc1ffc07c4 0x6ff003ff83ff80f8

def z977 : W := mkw 0x9ff7fedbc0205000 0xd3feffdb78040a00 0x9fffffffe0007807 0xd3fffffffc000f00

def z978 : W := mkw 0x0db7becbc0000000 0x01b6f7d978000000 0x9fffffffe0000007 0xd3fffffffc000000

def z979 : W := mkw 0x419988e170b262e8 0x0833311c2e164c5d 0x83b998e3e0f267f8 0xd077331c7c1e4cff

def z980 : W := mkw 0xac2e770abb038570 0x5585cee1576070ae 0xfc3e7f03ff0387ff 0x7f87cfe07fe070ff

def z981 : W := mkw 0x240815003b038570 0x048102a0076070ae 0xfc381f03ff0387ff 0x7f8703e07fe070ff

def z982 : W := mkw 0x9ff7fedbc0204000 0x53feffdb78040800 0x9fffffffe0f06007 0xd3fffffffc1e0c00

def z983 : W := mkw 0x419988e172b362e8 0x0833311c2e566c5d 0xe3b998e3fff3e7fe 0xfc77331c7ffe7cff

def z984 : W := mkw 0x9b7d4000166b5000 0x936fa80002cd6a00 0xffffe7fc1ffff807 0xfffffcff83ffff00

def z985 : W := mkw 0x9ff7fedbc0000000 0x53feffdb78000000 0x9fffffffe08c7807 0xd3fffffffc118f00

def z986 : W := mkw 0x0826a24b80000000 0x0104d44970000000 0x807fe7ffe0000003 0xd00ffcfffc000000

def z987 : W := mkw 0x0002a36f0884ae1c 0x0000546de11095c3 0xa07fffffe88ffe3f 0xf40ffffffd11ffc7

def z988 : W := mkw 0x0db7bedbc0000000 0x41b6f7db78000000 0x9fbf9fffe0000007 0xd3f7f3fffc000000

def z989 : W := mkw 0x97d3fedbc0000000 0x52fa7fdb78000000 0x83f9ffffe0000006 0xd07f3ffffc000000

def z990 : W := mkw 0x0002a36f0984af1c 0x0000546de13095e3 0xe047e7ff1f8ffffb 0xfc08fcffe3f1ffff

def z991 : W := mkw 0x9ff7fedbc4480000 0x53feffdb78890000 0x9fffffffe0fc0007 0xd3fffffffc1f8000

def z992 : W := mkw 0x97d1fcd940000000 0x52fa3f9b28000000 0x9ff9ffffe0000007 0xd3ff3ffffc000000

def z993 : W := mkw 0x12480000166b5000 0x8249000002cd6a00 0xffc7e0001ffff807 0xbff8fc0003ffff00

def z994 : W := mkw 0x600801243fffe7f8 0x2c01002487fffcff 0x600000001fffe7f8 0x2c00000003fffcff

def z995 : W := mkw 0x9ff7fedbc2010000 0x53feffdb78402000 0xbfffffffef018007 0xd7fffffffde03000

def z996 : W := mkw 0x9ff7fedbc5480100 0x73feffdb78a90020 0x9fffffffe7000007 0xd3fffffffce00000

def z997 : W := mkw 0x16c01db40ddc0780 0x22d803b681bb80f0 0x7fc01ffc1f7c07c5 0x4ff803ff83ef80f8

def z998 : W := mkw 0x16c01db40ddcaf9c 0x22d803b681bb95f3 0x7fc01ffc1ffc07ff 0xeff803ff83ff80ff

def z999 : W := mkw 0x16c01c9005580180 0x22d8039200ab0030 0x7fc01ffc1ffc01c7 0xeff803ff83ff8038

def z1000 : W := mkw 0x0002a24b0000a81c 0x0000544960001503 0xa047e7ff088ff83b 0xf408fcffe111ff07

def z1001 : W := mkw 0x419988c1703260e8 0x083331182e064c1d 0xc3b99803f07267fe 0x787733007e0e4cff

def z1002 : W := mkw 0x16c01db40ddc0780 0x22d803b681bb80f0 0x5f801ffc17f007c6 0xebf003ff82fe00f8

def z1003 : W := mkw 0x2c2e370ebb078d74 0x0585c6e1d760f1ae 0xfc3e1f1fff0387ff 0x7f87c3e3ffe070ff

def z1004 : W := mkw 0x16c01db40ddc0780 0x22d803b681bb80f0 0x7fc1fffc1ffc7fc7 0xeff83fff83ff8ff8

def z1005 : W := mkw 0x419988e170b262e8 0x0833311c2e164c5d 0x43b998e3f0f067fc 0xc877331c7e1e0cff

def z1006 : W := mkw 0x04801da409940780 0x009003b4813280f0 0x7fc01ffc1ffc07c7 0xeff803ff83ff80f8

def z1007 : W := mkw 0x9bf7eacb40000000 0x137efd5968000000 0x9fffffffe0000007 0xd3fffffffc000000

def z1008 : W := mkw 0x0002a36f0884ae1c 0x0000546de11095c3 0xa047e7ff088ff839 0x9408fcffe111ff07

def z1009 : W := mkw 0xc199e8e970b262e8 0x58333d1d2e164c5d 0xc3b9f8e3f0f267fe 0xf8773f1c7e1e4cff

def z1010 : W := mkw 0x9ff7fedbc2011000 0xd3feffdb78402200 0x9fffffffe0019807 0xd3fffffffc003300

def z1011 : W := mkw 0x9b7d4000166b5000 0x936fa80002cd6a00 0xffbfe0001ffff804 0x3ff7fc0003ffff00

def z1012 : W := mkw 0x0002a36f0884ae1c 0x0000546de11095c3 0xe3c7e7ff18fffe3f 0xfc78fcffe31fffc7

def z1013 : W := mkw 0x9ff7fedbc0000000 0x53feffdb78000000 0xdffffffff0f00007 0xfbfffffffe1e0000

def z1014 : W := mkw 0xd3d1e8fd44fc6288 0x7a7a3d1fa89f8c51 0x03c1e0fc00fc6000 0x80783c1f801f8c00

def z1015 : W := mkw 0x9ff7fedbc6491000 0xd3feffdb78c92200 0xfffffffffffd9807 0xffffffffffffb300

def z1016 : W := mkw 0x0008000030020060 0x000100000600400c 0xc3b81803f0f207fe 0xf87703007e1e40ff

def z1017 : W := mkw 0x8db7fedbc0000000 0x51b6ffdb78000000 0x9c3fffffe0000007 0x5387fffffc000000

def z1018 : W := mkw 0x200801243a87ae7c 0x040100248750f5cf 0x20000000088ffe38 0x240000000111ffc7

def z1019 : W := mkw 0x3e6617128f498510 0x27ccc2e251e930a2 0x3c0607000f018001 0x0780c0e001e03000

def z1020 : W := mkw 0xdff7fedbc0304080 0x5bfeffdb78060810 0x9fffffffe0700007 0xd3fffffffc0e0000

def z1021 : W := mkw 0x9b7d4000166b5000 0x936fa80002cd6a00 0xbfffe0000ffff801 0x97fffc0001ffff00

def z1022 : W := mkw 0x0002a34b08008410 0x0000546961001082 0xa047e7ff088ffe3b 0xf408fcffe111ffc7

def z1023 : W := mkw 0x17d3bedb40000000 0x02fa77db68000000 0x9fffffffe0000007 0xd3fffffffc000000

def z1024 : W := mkw 0xbffd5c90b77b51e0 0xb7ffab9216ef6a3c 0x5fb81800f77001c4 0x0bf703001eee0038

def z1025 : W := mkw 0x9ff7fedbc0000000 0x53feffdb78000000 0x9c7fffffe0000001 0x538ffffffc000000

def z1026 : W := mkw 0x9ff7fedbc0002008 0x53feffdb78000401 0x9fffffffe002603f 0xd3fffffffc004c07

def z1027 : W := mkw 0x9b7d4000166b5000 0x936fa80002cd6a00 0x7fc7e0001ffff801 0xaff8fc0003ffff00

def z1028 : W := mkw 0x0c26170289008510 0x0184c2e0512010a2 0xfc3e1f03ff0387ff 0x7f87c3e07fe070ff

def z1029 : W := mkw 0x3e6617028f498510 0x07ccc2e051e930a2 0x3c4607000f0d8001 0x0788c0e001e1b000

def z1030 : W := mkw 0x0002a36f0884ae1c 0x0000546de11095c3 0x2047e7fc088ffe39 0xa408fcff8111ffc7

def z1031 : W := mkw 0x9ff75e92c0000000 0x53feebd258000000 0x9ffe1fffe0000007 0xd3ffc3fffc000000

def z1032 : W := mkw 0x9bf7eadbc0000000 0x537efd5b78000000 0x83ffe7ffe0000003 0xd07ffcfffc000000

def z1033 : W := mkw 0x9ff7fedbc0000000 0x53feffdb78000000 0xdffffffff00007c7 0xfbfffffffe0000f8

def z1034 : W := mkw 0xbe66770e8f4d9d14 0x97cccee1d1e9b3a2 0x3c46671c0f0d9801 0x0788cce381e1b300

def z1035 : W := mkw 0x2c2e1702bb038570 0x0585c2e0576070ae 0xfc7e7f03ff0f9fff 0x7f8fcfe07fe1f3ff

def z1036 : W := mkw 0x2c2e1702bb038570 0x0585c2e0576070ae 0xdc381f03f70207fe 0x7b8703e07ee040ff

def z1037 : W := mkw 0x0119000030224060 0x002320000604480c 0xc3b81803f07207fe 0x787703007e0e40ff

def z1038 : W := mkw 0x0002a36f0994af9c 0x2000546de13295f3 0xa047e7ff088ffffb 0xf408fcffe111ffff

def z1039 : W := mkw 0x16c01db40ddc2f8c 0x22d803b681bb85f1 0x7fc01ffc1ffc7fc7 0xeff803ff83ff8ff8

def z1040 : W := mkw 0x9ff5fcd9c0000000 0x53febf9b38000000 0x1ff9fffce0000007 0xc3ff3fff9c000000

def z1041 : W := mkw 0x419988e170b262e8 0x0833311c2e164c5d 0xc3b818e3f07207fe 0x7877031c7e0e40ff

def z1042 : W := mkw 0x4199a8ed70b66aec 0x0833351dae16cd5d 0xc3b998fff0f267fe 0xf877331ffe1e4cff

def z1043 : W := mkw 0x419988e172b372e8 0x8833311c2e566e5d 0xc3b998e3f0f3fffe 0xf877331c7e1e7fff

def z1044 : W := mkw 0x4199a8ed70b66aec 0x0833351dae16cd5d 0xe3fff8fff8ffffff 0xfc7fff1fff1fffff

def z1045 : W := mkw 0x2c2c1500bb038570 0x058582a0176070ae 0xfc381803ff0387fe 0x7f8703007fe070ff

def z1046 : W := mkw 0x0000816508842608 0x0000102ca11084c1 0xa047e7ff088ffe3b 0xf408fcffe111ffc7

def z1047 : W := mkw 0x16c01cb004d80280 0x02d80396009b0050 0x7fc01ffc1ffc07c7 0xeff803ff83ff80f8

def z1048 : W := mkw 0x008888e1309222e8 0x0011111c2612445d 0xc3b998e3f0f267fe 0xf877331c7e1e4cff

def z1049 : W := mkw 0x9ff7fedbc6491000 0xd3feffdb78c92200 0x9fffffffe7000007 0xd3fffffffce00000

def z1050 : W := mkw 0x16c01c9000000000 0x02d8039200000000 0x9ff81fffe0000007 0xd3ff03fffc000000

def z1051 : W := mkw 0x0c2e1602b2030060 0x0185c2c05640600c 0xfc3e1f03ff0387ff 0x7f87c3e07fe070ff

def z1052 : W := mkw 0x9b7d4000d66b5000 0xd36fa8001acd6a00 0xffffe000fffff807 0xbffffc001fffff00

def z1053 : W := mkw 0x2c2e1716bb078570 0x2585c2e2d760f0ae 0xfc3e1f1fff0387ff 0x7f87c3e3ffe070ff

def z1054 : W := mkw 0x9b7d4000166b5000 0x936fa80002cd6a00 0x7fffe0001ffdf805 0x8ffffc0003ffbf00

def z1055 : W := mkw 0x6482bfefe994affc 0x0c9057fdfd3295ff 0x00001fffe00007f8 0x400003fffc0000ff

def z1056 : W := mkw 0x16c01db40ddc0780 0x22d803b681bb80f0 0xffc19ffc1ffe67c7 0xfff833ff83ffccf8

def z1057 : W := mkw 0x16c01db009900780 0x02d803b6013200f0 0x7fc01ffc1ff007c7 0xeff803ff83fe00f8

def z1058 : W := mkw 0xc93fe24bf2237068 0xd927fc497e446e0d 0x803fe003e003f838 0x1007fc007c007f07

def z1059 : W := mkw 0x2c2e1702bb038570 0x0585c2e0576070ae 0xfc7e1f03ff8f87ff 0xff8fc3e07ff1f0ff

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z7,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z8,z5]),(0,[z9,z0,z1,z2,z3,z4,z5]),(0,[z0,z10,z1,z2,z3,z4,z5]),(0,[z0,z11,z1,z2,z3,z4,z5])],[(0,[z12,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z13]),(0,[z0,z1,z2,z14,z3,z4,z5]),(0,[z0,z15,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z16,z4,z17]),(0,[z0,z1,z2,z18,z3,z4,z5]),(0,[z0,z1,z2,z19,z3,z4,z20])],[(0,[z21,z0,z22,z1,z2,z3,z5]),(0,[z0,z1,z2,z23,z3,z4,z5]),(0,[z24,z0,z1,z2,z3,z4,z5]),(0,[z0,z25,z1,z2,z3,z5,z26]),(0,[z0,z1,z2,z3,z4,z27,z5])],[(0,[z0,z1,z2,z28,z3,z4,z5]),(1,[z0,z1,z2,z29,z3,z4]),(0,[z0,z30,z1,z2,z3,z4,z5]),(1,[z0,z31,z1,z32,z4,z5]),(0,[z0,z1,z2,z3,z5,z33,z34])],[(1,[z0,z1,z2,z35,z4,z5]),(0,[z36,z0,z1,z2,z3,z4,z37]),(1,[z38,z1,z2,z3,z4,z39]),(0,[z0,z1,z40,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z41,z4,z5]),(0,[z0,z1,z2,z3,z42,z4,z5])],[(0,[z0,z1,z2,z43,z3,z4,z5]),(0,[z44,z0,z1,z2,z3,z4,z45]),(0,[z46,z0,z1,z2,z47,z4,z5]),(0,[z36,z0,z48,z1,z2,z3,z4])],[(0,[z49,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z37,z20]),(0,[z0,z50,z1,z2,z3,z4,z5]),(0,[z51,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z52,z5]),(0,[z53,z0,z1,z54,z3,z4,z5]),(0,[z0,z55,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z56,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z57,z4,z5]),(0,[z0,z1,z58,z2,z3,z4,z5])],[(0,[z0,z59,z1,z2,z3,z4,z5]),(0,[z21,z0,z1,z2,z3,z60,z5])],[(0,[z0,z1,z2,z3,z4,z5,z61]),(0,[z0,z62,z1,z2,z3,z4,z5]),(0,[z63,z0,z1,z2,z3,z4,z5]),(0,[z64,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z65,z4,z5])],[(0,[z0,z1,z2,z66,z3,z4,z5]),(1,[z0,z67,z1,z2,z3,z4]),(0,[z0,z68,z1,z2,z3,z16,z4])],[(0,[z0,z1,z69,z2,z70,z3,z4]),(0,[z71,z0,z1,z2,z3,z4,z5]),(0,[z0,z22,z2,z3,z4,z5,z26]),(0,[z72,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z73,z2,z3,z4,z5])],[(0,[z0,z67,z1,z2,z3,z4,z5]),(0,[z74,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z75])],[(0,[z0,z76,z2,z3,z77,z4,z5]),(0,[z46,z0,z78,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z79,z4,z5])],[(0,[z0,z1,z80,z2,z3,z4,z5]),(0,[z0,z1,z2,z81,z3,z4,z5]),(0,[z0,z48,z1,z3,z4,z5,z82])]],
   [[(0,[z0,z1,z2,z3,z83,z4,z5]),(0,[z84,z0,z1,z2,z85,z4,z5]),(0,[z46,z0,z1,z86,z3,z4,z5]),(0,[z21,z1,z2,z3,z60,z4,z5]),(0,[z87,z0,z1,z88,z2,z3,z4]),(0,[z0,z1,z89,z2,z3,z90,z4]),(0,[z0,z1,z2,z3,z4,z5,z91]),(0,[z0,z92,z1,z2,z3,z93,z5]),(0,[z0,z94,z1,z2,z3,z4,z5])],[(0,[z0,z95,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z96,z3,z4,z5]),(0,[z0,z97,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z98,z93,z5]),(0,[z0,z99,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z100,z4,z5]),(1,[z0,z101,z1,z3,z5,z33])],[(0,[z0,z1,z2,z3,z4,z5,z13]),(0,[z0,z1,z2,z102,z3,z4,z5]),(1,[z0,z92,z1,z2,z5,z34]),(0,[z0,z1,z2,z3,z4,z5,z103])],[(0,[z0,z1,z54,z2,z3,z4,z5]),(0,[z0,z104,z1,z2,z3,z4,z5]),(0,[z0,z1,z105,z2,z106,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z107]),(0,[z0,z1,z2,z3,z4,z5,z108]),(0,[z0,z1,z2,z3,z4,z5,z109])],[(0,[z0,z1,z2,z3,z110,z4,z5])],[(1,[z0,z1,z111,z3,z4,z5]),(0,[z0,z1,z2,z3,z112,z4,z5]),(0,[z0,z113,z1,z2,z3,z4,z5]),(1,[z0,z68,z1,z2,z3,z4]),(0,[z0,z94,z1,z3,z4,z5,z34]),(0,[z0,z114,z1,z2,z3,z5,z20])],[(0,[z0,z115,z1,z40,z3,z4,z5]),(0,[z0,z116,z1,z2,z90,z4,z5]),(1,[z0,z117,z1,z2,z4,z118])]],
   [[(0,[z0,z1,z2,z119,z3,z4,z5]),(0,[z0,z120,z1,z2,z70,z3,z4]),(0,[z46,z0,z1,z2,z3,z4,z121]),(0,[z46,z0,z22,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z4,z122,z5]),(0,[z123,z0,z1,z2,z3,z4,z5])],[(0,[z124,z0,z76,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z125,z4,z5]),(0,[z126,z0,z1,z2,z3,z4,z5]),(0,[z0,z127,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z128,z3,z4,z5]),(0,[z0,z1,z129,z2,z3,z4,z5]),(0,[z130,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z89,z2,z3,z4]),(0,[z0,z1,z58,z2,z3,z5,z33])],[(0,[z131,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z88,z3,z132,z4,z5]),(0,[z0,z133,z1,z2,z3,z4,z5])],[(0,[z0,z31,z1,z2,z85,z4,z5]),(0,[z0,z1,z2,z3,z134,z4,z5]),(0,[z0,z1,z135,z2,z3,z4,z5]),(0,[z0,z136,z114,z1,z2,z3,z5])],[(0,[z87,z0,z1,z2,z3,z4,z137]),(1,[z0,z115,z40,z3,z4,z5]),(0,[z0,z25,z2,z3,z138,z4,z5]),(0,[z0,z117,z1,z2,z19,z4,z5]),(1,[z0,z1,z2,z19,z4,z139])],[(0,[z0,z140,z1,z2,z3,z4,z5]),(0,[z0,z141,z1,z2,z3,z4,z5]),(0,[z142,z0,z1,z2,z3,z4,z5]),(0,[z0,z31,z1,z2,z3,z143,z5]),(0,[z0,z1,z2,z3,z4,z5,z144]),(0,[z0,z1,z2,z3,z145,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z146])]],
   [[(1,[z0,z22,z2,z3,z5,z26]),(0,[z0,z1,z2,z3,z4,z147,z5]),(0,[z0,z1,z148,z3,z32,z4,z5]),(0,[z0,z149,z1,z2,z3,z4,z5])],[(0,[z44,z0,z1,z2,z3,z4,z150]),(1,[z151,z1,z2,z85,z4,z5]),(0,[z0,z1,z2,z3,z152,z4,z5]),(0,[z0,z22,z1,z2,z3,z138,z5]),(0,[z0,z1,z153,z2,z3,z4,z5]),(0,[z0,z1,z2,z4,z139,z5,z118]),(0,[z0,z1,z2,z3,z154,z4,z5])],[(0,[z0,z1,z2,z3,z155,z4,z5])],[(0,[z44,z0,z1,z2,z3,z4,z5]),(0,[z0,z156,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z157]),(0,[z0,z1,z3,z132,z4,z5,z82]),(0,[z0,z158,z1,z2,z3,z4,z5])],[],[(0,[z0,z159,z1,z160,z2,z3,z5]),(0,[z0,z1,z2,z2,z3,z4,z5]),(0,[z0,z1,z78,z2,z3,z4,z5]),(0,[z38,z0,z1,z2,z3,z77,z4])],[(0,[z161,z0,z1,z2,z3,z4,z5]),(0,[z0,z116,z1,z2,z162,z4,z5]),(0,[z163,z0,z1,z2,z3,z4,z5])],[(1,[z0,z1,z164,z2,z3,z4]),(0,[z0,z1,z2,z3,z77,z4,z5]),(0,[z0,z165,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z166]),(0,[z0,z1,z2,z3,z4,z5,z167]),(0,[z0,z1,z168,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z169,z2,z3,z4,z5]),(0,[z0,z31,z1,z105,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z39,z5])],[(0,[z151,z0,z1,z2,z85,z4,z5]),(0,[z0,z31,z1,z2,z3,z170,z5]),(0,[z0,z31,z1,z3,z32,z4,z5]),(0,[z171,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z172,z4,z5])],[(0,[z0,z1,z2,z3,z85,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z173]),(0,[z0,z1,z2,z3,z174,z4,z5]),(0,[z0,z1,z2,z3,z4,z175,z5]),(0,[z176,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z177,z3,z4,z5])],[(0,[z0,z1,z2,z70,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z178]),(0,[z179,z0,z1,z2,z3,z4,z5])],[(0,[z0,z180,z1,z2,z3,z4,z5]),(1,[z0,z181,z2,z3,z4,z137]),(0,[z0,z1,z2,z3,z182,z5,z20])],[(0,[z0,z1,z2,z3,z4,z183,z5]),(0,[z184,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z185,z4,z5])]],
   [[(0,[z0,z25,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z186]),(0,[z0,z1,z2,z3,z4,z187,z5]),(0,[z0,z1,z2,z98,z3,z5,z34])],[(1,[z0,z1,z3,z4,z5,z108])],[(0,[z0,z1,z2,z3,z188,z4,z5])],[(0,[z0,z1,z2,z3,z189,z4,z5]),(0,[z0,z1,z190,z2,z3,z4,z5]),(0,[z0,z1,z191,z2,z3,z4,z5]),(0,[z0,z1,z105,z2,z93,z4,z5]),(0,[z0,z192,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z193,z4,z5]),(0,[z0,z1,z2,z194,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z195]),(1,[z0,z136,z114,z1,z2,z3])],[(0,[z0,z76,z2,z3,z4,z5,z26]),(0,[z53,z196,z1,z2,z3,z4,z5]),(0,[z197,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z198,z4,z5]),(0,[z0,z199,z1,z2,z4,z5,z33])],[(0,[z44,z76,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z200]),(0,[z46,z1,z2,z3,z4,z201,z5])],[(0,[z0,z202,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z203,z5]),(0,[z0,z1,z2,z148,z3,z4,z5]),(0,[z0,z1,z2,z3,z204,z4,z5]),(0,[z0,z117,z1,z2,z3,z4,z139])]],
   [[(0,[z0,z1,z2,z3,z4,z205,z5]),(0,[z206,z0,z1,z2,z3,z4,z5]),(0,[z0,z207,z1,z2,z3,z4,z5]),(0,[z0,z208,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z4,z5]),(0,[z0,z1,z2,z3,z209,z4,z5]),(0,[z0,z116,z210,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z211,z5]),(0,[z0,z1,z2,z3,z212,z4,z5]),(0,[z0,z1,z213,z2,z3,z4,z5])],[(0,[z0,z1,z54,z3,z4,z5,z33]),(1,[z0,z25,z2,z3,z138,z5]),(0,[z0,z1,z2,z3,z4,z5,z214]),(0,[z0,z215,z1,z2,z3,z4,z5])],[(0,[z216,z0,z1,z2,z3,z4,z5]),(0,[z0,z217,z1,z2,z3,z4,z5]),(0,[z38,z0,z1,z2,z19,z3,z4]),(0,[z0,z1,z2,z3,z218,z4,z5]),(0,[z0,z1,z2,z3,z16,z93,z5])],[(0,[z0,z1,z2,z219,z3,z4,z5]),(0,[z84,z0,z1,z220,z3,z4,z5])],[(1,[z0,z221,z222,z3,z4,z5]),(0,[z0,z1,z223,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z224,z5]),(0,[z0,z1,z2,z3,z4,z5,z225]),(0,[z0,z1,z2,z3,z226,z4,z5])],[(0,[z0,z1,z227,z2,z3,z4,z5]),(0,[z0,z1,z2,z98,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z228,z5]),(0,[z0,z1,z2,z3,z4,z5,z229]),(0,[z0,z1,z2,z3,z4,z230,z5])]],
   [[(0,[z231,z0,z1,z2,z3,z4,z5]),(0,[z0,z232,z1,z2,z3,z4,z5]),(0,[z0,z116,z2,z3,z90,z4,z5]),(0,[z0,z210,z2,z162,z3,z4,z5]),(0,[z0,z31,z1,z3,z16,z4,z5])],[(0,[z38,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z233,z3,z90,z4])],[(1,[z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z234,z4,z5]),(0,[z235,z0,z1,z2,z3,z4,z5]),(1,[z0,z116,z2,z90,z4,z5]),(0,[z236,z0,z1,z2,z3,z4,z5]),(0,[z0,z117,z1,z2,z4,z5,z118])],[(0,[z0,z1,z2,z237,z3,z4,z5]),(0,[z238,z0,z1,z2,z3,z4,z5]),(0,[z0,z181,z1,z2,z3,z77,z4]),(0,[z0,z1,z2,z3,z4,z5,z239]),(0,[z0,z1,z2,z3,z4,z5,z240])],[(0,[z241,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z242,z4,z5]),(0,[z0,z1,z2,z3,z4,z243,z5])],[(0,[z0,z1,z2,z3,z4,z244,z5]),(0,[z245,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z246,z5]),(0,[z0,z1,z220,z2,z3,z4,z5]),(0,[z0,z1,z2,z162,z3,z4,z5]),(0,[z0,z117,z1,z2,z3,z4,z20]),(0,[z0,z1,z2,z3,z4,z247,z5])],[(0,[z248,z0,z1,z2,z3,z4,z5]),(0,[z0,z249,z1,z2,z3,z4,z5]),(0,[z0,z141,z1,z2,z222,z4,z5]),(0,[z0,z1,z2,z250,z3,z4,z5]),(0,[z0,z22,z1,z2,z3,z4,z251]),(0,[z0,z117,z181,z1,z2,z3,z4])],[(1,[z0,z120,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z252,z5])]],
   [[(0,[z0,z76,z1,z2,z3,z253,z4]),(0,[z0,z254,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z143,z4,z5]),(0,[z0,z1,z255,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z256,z4,z5])],[(0,[z0,z1,z2,z3,z257,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z258]),(0,[z0,z1,z2,z3,z4,z5,z259]),(0,[z0,z260,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z261,z3,z4,z5]),(0,[z0,z262,z1,z2,z3,z4,z5]),(0,[z0,z114,z48,z1,z2,z3,z4])],[(1,[z36,z0,z2,z3,z77,z4]),(0,[z36,z0,z1,z2,z19,z3,z4])],[(0,[z0,z1,z2,z3,z253,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z37]),(1,[z0,z1,z2,z3,z170,z5]),(0,[z0,z263,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z82]),(0,[z0,z1,z2,z3,z4,z139,z5]),(0,[z0,z1,z2,z3,z264,z4,z5])],[],[(0,[z0,z1,z2,z265,z3,z4,z5]),(1,[z196,z1,z70,z3,z4,z5]),(0,[z0,z1,z266,z2,z3,z4,z5])],[(0,[z0,z267,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z268,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z26]),(0,[z0,z92,z1,z2,z3,z5,z34])],[(0,[z21,z0,z25,z1,z2,z3,z5]),(0,[z0,z221,z1,z222,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z269]),(0,[z0,z1,z270,z2,z3,z4,z5]),(0,[z0,z1,z271,z2,z3,z4,z5])]],
   [[(0,[z272,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z273,z3,z4,z5]),(0,[z0,z1,z2,z3,z274,z4,z5]),(0,[z0,z275,z1,z2,z3,z4,z5]),(0,[z36,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z105,z2,z32,z4,z5])],[(0,[z0,z276,z1,z2,z3,z4,z5]),(1,[z0,z48,z1,z3,z4,z82]),(0,[z0,z1,z2,z3,z4,z5,z118])],[(0,[z0,z76,z1,z2,z3,z4,z277]),(1,[z0,z1,z3,z198,z4,z5]),(0,[z0,z1,z278,z2,z3,z4,z5]),(0,[z0,z1,z279,z2,z3,z4,z5]),(0,[z0,z280,z1,z2,z3,z4,z5])],[(0,[z281,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z282,z2,z3,z4,z5]),(0,[z87,z0,z117,z1,z2,z3,z4]),(0,[z0,z283,z1,z2,z3,z4,z5])],[(0,[z21,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z60,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z5]),(0,[z0,z1,z284,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z285,z5]),(0,[z0,z1,z2,z3,z93,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z286]),(0,[z0,z1,z2,z19,z3,z4,z118])],[(0,[z0,z1,z287,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z288]),(0,[z0,z1,z2,z3,z289,z4,z5]),(1,[z0,z94,z1,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z290,z5]),(0,[z0,z181,z1,z2,z3,z4,z37]),(0,[z0,z1,z2,z291,z3,z4,z5]),(0,[z0,z101,z1,z2,z3,z16,z5]),(0,[z0,z68,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z182,z4,z20])],[(0,[z292,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z293,z3,z4,z5]),(0,[z0,z1,z2,z19,z3,z4,z5])]],
   [[(0,[z38,z0,z1,z2,z3,z4,z39]),(0,[z294,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z105,z148,z3,z4,z5]),(0,[z0,z1,z88,z2,z3,z4,z20])],[(0,[z0,z1,z2,z295,z3,z4,z5]),(0,[z0,z1,z296,z2,z3,z4,z5])],[(0,[z0,z297,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z298,z4,z5]),(0,[z0,z1,z2,z3,z4,z299,z5]),(0,[z0,z1,z2,z3,z300,z4,z5]),(0,[z0,z1,z301,z2,z3,z4,z5]),(0,[z302,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z303,z3,z4,z5])],[(0,[z0,z115,z40,z2,z3,z4,z5]),(0,[z304,z0,z1,z2,z3,z4,z5]),(0,[z0,z305,z1,z2,z3,z4,z5])],[(0,[z76,z1,z160,z2,z3,z4,z5]),(0,[z53,z0,z1,z2,z306,z4,z5]),(0,[z46,z21,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z307,z4,z5]),(0,[z0,z1,z2,z3,z4,z308,z5]),(0,[z0,z92,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z309,z3,z4,z5]),(0,[z84,z0,z1,z2,z106,z4,z5]),(0,[z0,z310,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z311,z5])],[(0,[z44,z0,z76,z2,z3,z4,z5]),(0,[z0,z312,z1,z2,z3,z4,z5]),(0,[z0,z31,z116,z1,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z313])],[(0,[z0,z314,z1,z2,z3,z4,z5]),(0,[z0,z315,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z5,z316]),(0,[z0,z1,z317,z2,z3,z4,z5]),(1,[z0,z1,z105,z148,z4,z5]),(0,[z0,z1,z3,z16,z4,z5,z33])],[(0,[z0,z1,z318,z2,z3,z4,z5]),(0,[z319,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z320,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z321]),(0,[z0,z136,z1,z2,z3,z182,z5])],[(0,[z46,z0,z1,z2,z3,z60,z5]),(0,[z0,z116,z1,z105,z2,z4,z5]),(0,[z0,z322,z1,z2,z3,z4,z5]),(0,[z323,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z324,z5]),(0,[z0,z325,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z326,z5]),(0,[z0,z327,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z328,z3,z4,z5])],[(0,[z0,z1,z2,z3,z329,z4,z5]),(0,[z0,z1,z3,z198,z90,z4,z5])],[(0,[z196,z1,z2,z70,z3,z4,z5]),(0,[z330,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z201,z5]),(0,[z0,z1,z2,z3,z4,z331,z5]),(0,[z0,z1,z2,z332,z3,z4,z5])],[(0,[z0,z1,z2,z3,z333,z4,z5])],[(0,[z0,z1,z334,z2,z3,z4,z5]),(0,[z0,z335,z1,z2,z3,z4,z5]),(0,[z0,z1,z336,z2,z3,z4,z5])],[(0,[z0,z181,z160,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z45]),(0,[z0,z1,z337,z2,z3,z4,z5]),(0,[z0,z1,z2,z106,z3,z4,z5]),(0,[z36,z0,z1,z2,z3,z4,z39]),(0,[z0,z1,z2,z3,z4,z5,z338]),(0,[z0,z1,z339,z2,z3,z4,z5])]],
   [[(0,[z340,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z341,z3,z4,z5]),(0,[z342,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z343,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z344,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z345]),(1,[z0,z1,z220,z3,z4,z5]),(0,[z0,z31,z1,z2,z106,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z346]),(0,[z0,z347,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z348,z4,z5])],[(1,[z53,z1,z54,z3,z4,z5]),(0,[z46,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z349,z3,z4,z5]),(0,[z350,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z58,z3,z16,z4,z5])],[(0,[z0,z25,z76,z2,z3,z4,z5]),(0,[z0,z1,z2,z351,z3,z4,z5]),(0,[z0,z67,z1,z2,z3,z85,z4]),(0,[z0,z352,z1,z3,z90,z4,z5]),(0,[z0,z1,z2,z353,z3,z4,z5])],[(0,[z0,z1,z2,z3,z35,z4,z5]),(0,[z46,z0,z1,z2,z3,z4,z13]),(1,[z0,z1,z2,z233,z3,z4]),(0,[z354,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z355]),(0,[z0,z356,z1,z2,z3,z93,z4])],[(0,[z0,z1,z70,z148,z3,z4,z5]),(0,[z0,z1,z2,z3,z357,z4,z5])],[(0,[z358,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z34])],[(0,[z0,z1,z359,z2,z3,z4,z5]),(0,[z0,z360,z1,z2,z3,z4,z5]),(0,[z0,z361,z1,z2,z3,z4,z5])]],
   [[(1,[z0,z1,z2,z3,z362,z4]),(0,[z0,z1,z363,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z364]),(0,[z0,z365,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z366,z4,z5]),(0,[z367,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z368,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z369]),(0,[z0,z1,z2,z3,z4,z5,z370]),(0,[z0,z371,z1,z2,z3,z4,z5]),(0,[z0,z372,z1,z2,z3,z4,z5])],[(0,[z0,z1,z373,z2,z3,z4,z5]),(0,[z87,z1,z2,z3,z4,z5,z37])],[(0,[z0,z1,z2,z3,z374,z4,z5]),(0,[z87,z0,z1,z2,z3,z4,z37]),(0,[z375,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z376,z2,z3,z4,z5])],[(0,[z87,z0,z48,z1,z2,z3,z4])],[(0,[z0,z1,z377,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z378,z4,z5]),(0,[z0,z221,z115,z2,z3,z4,z5]),(1,[z0,z199,z1,z2,z4,z5])],[(0,[z0,z379,z1,z2,z3,z4,z5]),(0,[z151,z0,z1,z2,z106,z4,z5]),(0,[z0,z1,z2,z380,z3,z4,z5]),(0,[z0,z1,z2,z381,z3,z4,z5]),(0,[z0,z92,z1,z2,z98,z4,z5])]],
   [[(0,[z0,z1,z2,z382,z3,z4,z5]),(0,[z0,z1,z2,z3,z383,z4,z5]),(1,[z0,z210,z2,z162,z4,z5]),(0,[z0,z114,z1,z2,z3,z77,z4]),(0,[z0,z1,z2,z3,z384,z4,z5]),(0,[z0,z1,z2,z3,z4,z385,z5])],[(0,[z0,z1,z2,z3,z4,z5,z386]),(0,[z0,z387,z1,z2,z3,z4,z5]),(0,[z388,z0,z1,z2,z3,z4,z5])],[(0,[z0,z389,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z390,z4,z5]),(0,[z391,z0,z1,z2,z3,z4,z5])],[(0,[z0,z392,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z393,z5]),(0,[z0,z1,z2,z394,z3,z4,z5]),(0,[z0,z1,z395,z2,z3,z4,z5]),(0,[z396,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z98,z85,z4,z5]),(0,[z0,z210,z1,z2,z3,z4,z5]),(0,[z0,z1,z397,z2,z3,z4,z5])],[(0,[z0,z398,z1,z2,z3,z4,z5])],[(0,[z0,z399,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z400]),(0,[z401,z0,z1,z2,z3,z4,z5])],[(0,[z151,z1,z2,z3,z85,z4,z5]),(0,[z21,z0,z1,z2,z3,z201,z5]),(0,[z0,z402,z1,z2,z3,z4,z5]),(0,[z0,z403,z1,z2,z3,z4,z5])]],
   [[(0,[z1,z54,z2,z70,z3,z4,z5]),(0,[z0,z1,z2,z3,z404,z4,z5]),(0,[z0,z1,z2,z3,z4,z405,z5])],[(0,[z0,z1,z406,z2,z3,z4,z5]),(0,[z0,z356,z1,z2,z3,z4,z5])],[(1,[z84,z1,z2,z106,z4,z5]),(0,[z0,z22,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z143,z5]),(0,[z0,z1,z88,z2,z3,z132,z4]),(0,[z0,z1,z2,z407,z3,z4,z5])],[(1,[z0,z1,z2,z3,z4,z150]),(0,[z408,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z409,z2,z3,z4,z5])],[(0,[z0,z1,z2,z410,z3,z4,z5]),(0,[z0,z411,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z412])],[(0,[z0,z31,z210,z1,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z170,z5]),(0,[z0,z1,z2,z3,z4,z5,z413])],[(0,[z414,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z415,z4,z5]),(0,[z0,z1,z58,z2,z3,z16,z5])],[(0,[z0,z1,z2,z3,z416,z4,z5]),(1,[z0,z389,z2,z3,z4,z5]),(0,[z0,z1,z2,z417,z3,z4,z5]),(0,[z0,z1,z2,z3,z418,z4,z5]),(0,[z0,z1,z2,z3,z16,z4,z5]),(0,[z0,z1,z2,z3,z419,z4,z5]),(0,[z0,z1,z2,z3,z420,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z421,z4,z5]),(0,[z0,z422,z1,z2,z3,z4,z5]),(0,[z0,z31,z1,z2,z93,z4,z5]),(0,[z0,z1,z2,z3,z423,z4,z5])],[(0,[z0,z1,z160,z2,z3,z4,z5]),(0,[z0,z424,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z425,z3,z4,z5]),(0,[z0,z426,z1,z2,z3,z4,z5]),(0,[z0,z1,z105,z2,z3,z4,z5]),(0,[z427,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z428,z3,z4,z5]),(0,[z0,z1,z429,z2,z3,z4,z5])],[(0,[z0,z430,z1,z2,z3,z4,z5]),(0,[z0,z114,z1,z2,z3,z4,z37]),(0,[z0,z1,z2,z3,z362,z4,z5]),(1,[z0,z356,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z5,z431]),(0,[z0,z432,z1,z2,z3,z4,z5]),(0,[z0,z1,z433,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z434,z5])],[],[(0,[z0,z435,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z33]),(0,[z0,z1,z2,z436,z3,z4,z5]),(0,[z0,z114,z1,z2,z19,z3,z4])],[(0,[z0,z1,z2,z3,z4,z437,z5]),(0,[z0,z438,z1,z2,z3,z4,z5]),(0,[z0,z181,z2,z3,z4,z5,z137]),(0,[z0,z439,z1,z2,z3,z4,z5])]],
   [[(0,[z440,z0,z1,z2,z3,z4,z5]),(0,[z441,z0,z1,z2,z3,z4,z5]),(0,[z38,z0,z442,z2,z3,z4,z5]),(0,[z0,z115,z1,z222,z3,z4,z5]),(0,[z0,z1,z2,z3,z443,z4,z5]),(0,[z0,z1,z2,z3,z444,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z445]),(0,[z0,z136,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z446,z4,z5]),(0,[z0,z1,z2,z3,z4,z121,z5]),(1,[z0,z442,z2,z3,z4,z5]),(0,[z38,z0,z1,z88,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z5,z447]),(0,[z0,z448,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z449,z3,z4,z5]),(0,[z0,z450,z1,z2,z3,z4,z5]),(0,[z0,z451,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z452,z5])],[(1,[z0,z352,z1,z3,z4,z5]),(0,[z0,z1,z2,z3,z132,z4,z5])],[(0,[z453,z0,z1,z2,z3,z4,z5]),(1,[z0,z141,z1,z2,z4,z5]),(0,[z0,z48,z1,z2,z3,z4,z20]),(0,[z0,z1,z454,z2,z3,z4,z5])],[(0,[z0,z1,z2,z455,z3,z4,z5]),(1,[z0,z424,z1,z2,z3,z5]),(0,[z196,z0,z1,z70,z3,z4,z5]),(0,[z0,z48,z181,z1,z2,z3,z4]),(0,[z0,z199,z1,z2,z3,z4,z5]),(0,[z0,z114,z1,z2,z3,z4,z5])],[(0,[z456,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z150]),(0,[z46,z0,z1,z2,z3,z201,z5]),(0,[z0,z1,z2,z3,z4,z5,z457]),(0,[z0,z1,z2,z3,z4,z5,z458])],[(0,[z0,z1,z2,z3,z4,z459,z5]),(0,[z0,z136,z114,z1,z2,z3,z4])],[(0,[z0,z460,z1,z2,z3,z4,z5]),(0,[z0,z1,z164,z2,z222,z3,z4]),(0,[z0,z1,z461,z2,z3,z4,z5]),(0,[z0,z22,z1,z2,z3,z5,z26]),(0,[z0,z1,z2,z3,z462,z4,z5])]],
   [[(0,[z0,z0,z1,z2,z3,z4,z5]),(0,[z463,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z464,z2,z3,z4]),(0,[z0,z117,z1,z2,z3,z4,z118]),(0,[z0,z465,z1,z2,z3,z4,z5])],[(0,[z466,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z467,z3,z4,z5])],[(0,[z0,z1,z2,z222,z3,z4,z5]),(0,[z0,z1,z2,z468,z3,z4,z5]),(0,[z0,z1,z469,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z470,z5]),(0,[z0,z1,z2,z471,z3,z4,z5]),(1,[z0,z1,z472,z3,z4,z5]),(0,[z0,z1,z89,z2,z3,z4,z5])],[(0,[z0,z160,z2,z3,z4,z5,z26]),(0,[z36,z0,z181,z2,z3,z4,z5]),(0,[z0,z181,z1,z2,z19,z3,z4]),(0,[z0,z31,z101,z1,z3,z4,z5]),(0,[z0,z48,z1,z88,z3,z4,z5])],[(0,[z0,z1,z473,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z474,z5]),(0,[z0,z1,z2,z93,z4,z5,z34])],[(0,[z0,z475,z1,z2,z3,z4,z5]),(0,[z38,z0,z1,z2,z3,z4,z137]),(0,[z0,z1,z2,z3,z476,z4,z5]),(0,[z0,z1,z2,z3,z477,z4,z5])],[(0,[z478,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z479,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z480]),(0,[z0,z481,z1,z2,z3,z4,z5])]],
   [[(0,[z482,z0,z1,z2,z3,z4,z5]),(0,[z0,z31,z221,z1,z3,z4,z5]),(0,[z0,z210,z1,z2,z90,z4,z5]),(0,[z36,z0,z1,z88,z2,z3,z4]),(0,[z36,z0,z117,z1,z2,z3,z4]),(0,[z483,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z105,z2,z148,z4,z5]),(0,[z0,z1,z2,z3,z484,z4,z5])],[(1,[z0,z159,z1,z2,z3,z5]),(0,[z151,z84,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z485,z3,z4,z5]),(0,[z0,z1,z486,z2,z3,z4,z5]),(0,[z0,z1,z2,z487,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z488])],[(0,[z0,z489,z1,z2,z3,z4,z5]),(0,[z0,z181,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z490,z4,z5])],[(0,[z124,z0,z160,z2,z3,z4,z5]),(0,[z0,z491,z1,z2,z3,z4,z5])],[(0,[z492,z0,z1,z2,z3,z4,z5]),(0,[z196,z0,z1,z54,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z493]),(0,[z87,z0,z1,z2,z3,z77,z4]),(0,[z0,z442,z1,z2,z3,z4,z5]),(0,[z0,z494,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z495,z4,z5])],[(0,[z496,z0,z1,z2,z3,z4,z5]),(0,[z0,z31,z1,z2,z32,z4,z5]),(0,[z0,z1,z88,z2,z3,z4,z82]),(0,[z0,z497,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z498,z4,z5]),(0,[z84,z0,z1,z111,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z499]),(0,[z500,z0,z1,z2,z3,z4,z5]),(0,[z0,z501,z1,z2,z3,z4,z5])],[(1,[z44,z76,z2,z3,z4,z5]),(0,[z0,z101,z1,z148,z3,z4,z5])]],
   [[(0,[z46,z0,z25,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z4,z502,z5])],[(0,[z503,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z504,z2,z3,z4,z5]),(0,[z0,z221,z1,z148,z3,z4,z5]),(0,[z0,z1,z2,z3,z93,z5,z33])],[(0,[z505,z0,z1,z2,z3,z4,z5])],[(0,[z0,z76,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z506,z4,z5]),(0,[z0,z114,z1,z2,z3,z4,z39]),(0,[z0,z1,z2,z3,z507,z4,z5]),(0,[z0,z1,z2,z508,z3,z4,z5]),(0,[z0,z509,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z510]),(0,[z0,z1,z2,z3,z4,z511,z5]),(0,[z0,z1,z2,z3,z4,z5,z512]),(0,[z0,z1,z2,z4,z5,z229,z33]),(1,[z0,z1,z58,z3,z16,z5]),(0,[z0,z1,z2,z3,z182,z4,z5])],[(0,[z36,z0,z1,z2,z3,z4,z137])],[(0,[z53,z1,z54,z2,z3,z4,z5]),(0,[z0,z1,z2,z513,z3,z4,z5]),(0,[z0,z1,z2,z3,z514,z4,z5]),(0,[z0,z1,z88,z2,z3,z4,z5]),(0,[z0,z1,z2,z515,z3,z4,z5]),(0,[z516,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z517,z2,z3,z4,z5]),(1,[z0,z1,z2,z306,z4,z5]),(0,[z1,z2,z106,z3,z85,z4,z5]),(0,[z0,z518,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z39,z5,z37]),(1,[z0,z1,z2,z519,z4,z5]),(0,[z0,z210,z1,z2,z162,z4,z5]),(0,[z0,z1,z2,z3,z520,z4,z5]),(0,[z0,z1,z521,z2,z3,z4,z5])]],
   [[(0,[z0,z221,z2,z222,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z522]),(0,[z0,z22,z1,z2,z3,z362,z4]),(0,[z0,z523,z1,z2,z3,z4,z5])],[(0,[z524,z0,z1,z2,z3,z4,z5]),(0,[z53,z0,z1,z2,z35,z4,z5]),(0,[z0,z1,z2,z3,z525,z4,z5]),(0,[z0,z1,z2,z3,z138,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z137]),(0,[z0,z526,z1,z2,z3,z4,z5]),(0,[z0,z527,z1,z2,z3,z4,z5]),(0,[z0,z528,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z519,z3,z4,z5]),(0,[z0,z529,z1,z2,z3,z4,z5]),(0,[z0,z530,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z531,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z532]),(0,[z36,z0,z2,z3,z77,z4,z5])],[(0,[z533,z0,z1,z2,z3,z4,z5]),(0,[z0,z534,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z535,z4,z5]),(0,[z0,z1,z164,z2,z3,z4,z5]),(0,[z0,z1,z464,z2,z222,z3,z4]),(0,[z0,z1,z2,z3,z536,z4,z5]),(0,[z0,z1,z2,z3,z32,z4,z5])],[(0,[z0,z1,z2,z537,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z108,z34]),(0,[z0,z1,z2,z19,z4,z139,z5])],[(0,[z0,z1,z2,z3,z538,z4,z5]),(0,[z0,z1,z2,z3,z539,z4,z5])],[(0,[z0,z540,z1,z2,z3,z4,z5]),(0,[z0,z2,z3,z138,z4,z5,z26]),(0,[z0,z541,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z160,z2,z3,z77,z4,z5]),(0,[z542,z0,z1,z2,z3,z4,z5]),(0,[z0,z543,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z544,z3,z4,z5])],[(1,[z124,z160,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z545,z5]),(0,[z0,z1,z2,z306,z3,z4,z5]),(0,[z0,z1,z2,z3,z546,z4,z5]),(0,[z0,z181,z1,z2,z3,z4,z39])],[(0,[z0,z159,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z547,z3,z4,z5]),(0,[z87,z0,z1,z2,z19,z3,z4])],[(0,[z548,z0,z1,z2,z3,z4,z5])],[(0,[z0,z549,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z16,z5,z34]),(1,[z0,z1,z2,z3,z4,z17])],[(1,[z0,z1,z69,z2,z3,z4]),(0,[z0,z1,z2,z3,z550,z4,z5]),(0,[z0,z31,z92,z1,z2,z4,z5]),(0,[z551,z0,z1,z2,z3,z4,z5]),(0,[z0,z48,z1,z2,z3,z132,z4]),(1,[z0,z1,z2,z3,z182,z20])],[(0,[z552,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z553,z4,z5])],[(0,[z0,z554,z1,z2,z3,z4,z5]),(0,[z0,z555,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z556,z3,z4,z5])]],
   [[(0,[z557,z0,z1,z2,z3,z4,z5]),(0,[z87,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z558,z4,z5]),(0,[z559,z0,z1,z2,z3,z4,z5])],[],[(0,[z0,z1,z2,z560,z3,z4,z5]),(1,[z0,z1,z2,z357,z4,z5]),(0,[z0,z561,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z562,z3,z4,z5]),(0,[z0,z352,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z563])],[(0,[z0,z1,z564,z2,z3,z4,z5]),(0,[z46,z0,z1,z472,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z565,z5]),(0,[z0,z1,z566,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z251]),(0,[z0,z1,z2,z3,z567,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z568])],[(0,[z0,z1,z1,z2,z3,z4,z5]),(0,[z0,z1,z70,z3,z4,z5,z33]),(0,[z0,z101,z1,z58,z3,z4,z5])],[(0,[z124,z44,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z569])],[(0,[z0,z570,z1,z2,z3,z4,z5]),(0,[z0,z571,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z572,z4,z5])],[(0,[z0,z1,z105,z2,z85,z4,z5])]],
   [[(0,[z573,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z574,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z575]),(0,[z0,z576,z1,z2,z3,z4,z5]),(0,[z0,z1,z577,z2,z3,z4,z5])],[(0,[z578,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z98,z106,z4,z5]),(0,[z0,z1,z2,z3,z579,z4,z5]),(0,[z0,z1,z580,z2,z3,z4,z5]),(1,[z0,z1,z88,z3,z132,z4]),(0,[z0,z1,z2,z581,z3,z4,z5])],[(0,[z0,z582,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z583,z5]),(0,[z584,z0,z1,z2,z3,z4,z5]),(0,[z585,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z86,z3,z4,z5]),(0,[z0,z1,z2,z3,z586,z4,z5]),(0,[z0,z92,z1,z105,z2,z4,z5])],[(0,[z0,z1,z2,z233,z3,z4,z5])],[(0,[z0,z1,z58,z70,z3,z4,z5]),(0,[z587,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z588])],[(0,[z0,z1,z2,z3,z4,z5,z589]),(0,[z0,z1,z2,z3,z90,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z17]),(0,[z0,z590,z1,z2,z3,z4,z5])],[(0,[z124,z1,z160,z2,z3,z4,z5]),(0,[z196,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z591,z2,z3,z4,z5]),(0,[z0,z25,z1,z2,z3,z138,z5]),(0,[z0,z1,z2,z3,z4,z5,z592]),(0,[z0,z1,z2,z3,z4,z5,z593]),(0,[z0,z1,z2,z3,z4,z5,z594])]],
   [[(0,[z0,z1,z2,z3,z4,z5,z595]),(0,[z0,z1,z596,z2,z3,z4,z5]),(0,[z0,z1,z597,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z598,z4,z5])],[(1,[z46,z1,z2,z3,z201,z5]),(0,[z0,z1,z464,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z77,z4,z20]),(0,[z0,z1,z2,z3,z4,z5,z599])],[(0,[z600,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z601,z4,z5]),(0,[z84,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z602,z2,z3,z4,z5]),(0,[z38,z1,z2,z3,z4,z39,z5]),(0,[z0,z603,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z604,z3,z4,z5])],[(0,[z0,z1,z2,z3,z605,z4,z5]),(0,[z0,z1,z2,z3,z4,z39,z20])],[(0,[z0,z1,z2,z3,z606,z4,z5]),(0,[z0,z1,z2,z3,z607,z4,z5]),(0,[z608,z0,z1,z2,z3,z4,z5]),(0,[z38,z0,z117,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z609,z4,z5]),(0,[z0,z2,z162,z3,z90,z4,z5]),(0,[z0,z1,z2,z3,z610,z4,z5]),(0,[z0,z1,z2,z3,z93,z4,z563]),(0,[z0,z1,z2,z3,z4,z5,z563]),(0,[z0,z611,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z251])],[(0,[z0,z221,z1,z40,z3,z4,z5]),(0,[z0,z612,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z613,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z614]),(0,[z615,z0,z1,z2,z3,z4,z5])],[(0,[z616,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z69,z2,z3,z4,z5]),(0,[z87,z0,z1,z2,z3,z4,z39]),(0,[z0,z1,z2,z617,z3,z4,z5]),(0,[z0,z1,z618,z2,z3,z4,z5]),(0,[z0,z619,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z4,z5,z229])]],
   [[(0,[z0,z1,z2,z85,z4,z5,z34]),(0,[z0,z115,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z620,z4,z5]),(0,[z0,z101,z1,z2,z3,z4,z5]),(0,[z0,z621,z1,z2,z3,z4,z5])],[],[(0,[z0,z1,z622,z2,z3,z4,z5]),(0,[z0,z221,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z519,z222,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z623]),(0,[z0,z1,z2,z3,z624,z4,z5])],[(0,[z0,z625,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z626]),(0,[z0,z627,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z628])],[(0,[z0,z181,z76,z2,z3,z4,z5]),(0,[z0,z1,z58,z54,z3,z4,z5]),(1,[z0,z1,z2,z47,z4,z5]),(0,[z0,z1,z2,z47,z3,z4,z5]),(0,[z0,z629,z1,z2,z3,z4,z5]),(0,[z0,z630,z1,z2,z3,z4,z5]),(0,[z0,z92,z1,z2,z4,z5,z34])],[(0,[z124,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z631,z4,z5]),(0,[z0,z632,z1,z2,z3,z4,z5]),(0,[z0,z2,z3,z77,z4,z5,z137]),(0,[z0,z31,z1,z2,z3,z4,z5]),(0,[z0,z117,z1,z2,z3,z4,z5])],[(1,[z0,z1,z2,z3,z253,z4]),(0,[z0,z1,z633,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z137,z20]),(0,[z0,z634,z1,z2,z3,z4,z5]),(0,[z0,z114,z1,z2,z3,z182,z4])]],
   [[(0,[z0,z1,z472,z2,z3,z4,z5]),(0,[z0,z635,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z636,z4,z5]),(0,[z0,z1,z2,z637,z3,z4,z5]),(0,[z0,z48,z1,z2,z3,z4,z82])],[(0,[z0,z1,z2,z3,z4,z5,z638])],[(0,[z0,z1,z2,z3,z4,z45,z5]),(0,[z0,z1,z2,z3,z639,z4,z5]),(0,[z0,z1,z2,z640,z3,z4,z5]),(0,[z0,z641,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z642,z3,z4,z5])],[(0,[z0,z120,z1,z2,z3,z4,z5]),(0,[z0,z1,z54,z148,z3,z4,z5]),(0,[z0,z1,z2,z29,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z643])],[(0,[z0,z1,z2,z3,z4,z644,z5]),(0,[z0,z645,z1,z2,z3,z4,z5]),(0,[z84,z1,z2,z106,z3,z4,z5]),(0,[z0,z1,z2,z3,z646,z4,z5]),(0,[z0,z1,z2,z3,z4,z647,z5]),(1,[z87,z1,z2,z3,z4,z37]),(0,[z0,z1,z648,z2,z3,z4,z5]),(0,[z0,z114,z1,z88,z2,z3,z4]),(0,[z0,z117,z114,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z5,z649]),(0,[z0,z1,z2,z3,z650,z4,z5])],[(0,[z0,z31,z1,z70,z3,z4,z5]),(1,[z0,z78,z2,z3,z4,z5]),(0,[z0,z1,z651,z2,z3,z4,z5])],[]],
   [[(0,[z44,z0,z160,z2,z3,z4,z5]),(0,[z652,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z106,z4,z5,z34]),(1,[z0,z1,z86,z3,z4,z5]),(0,[z0,z1,z2,z653,z3,z4,z5]),(0,[z0,z1,z2,z98,z93,z4,z5])],[(0,[z0,z654,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z277]),(1,[z21,z1,z2,z3,z60,z5]),(0,[z0,z48,z1,z2,z3,z4,z5])],[(0,[z46,z0,z1,z2,z357,z4,z5]),(0,[z0,z115,z1,z148,z3,z4,z5]),(0,[z0,z655,z1,z2,z3,z4,z5]),(0,[z0,z101,z1,z2,z3,z5,z33]),(0,[z0,z656,z1,z2,z3,z4,z5]),(0,[z657,z0,z1,z2,z3,z4,z5])],[(0,[z0,z210,z1,z105,z2,z4,z5]),(0,[z0,z658,z1,z2,z3,z4,z5])],[(0,[z151,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z659,z5]),(0,[z38,z87,z1,z2,z3,z4,z5]),(0,[z0,z40,z2,z222,z3,z4,z5]),(0,[z660,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z661,z4,z5]),(0,[z0,z1,z2,z3,z3,z4,z5])],[(0,[z0,z1,z2,z3,z662,z4,z5]),(0,[z0,z1,z2,z3,z663,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z664])],[(0,[z53,z0,z1,z2,z3,z4,z5]),(0,[z0,z665,z1,z2,z3,z4,z5]),(0,[z0,z666,z1,z2,z3,z4,z5])]],
   [[(1,[z0,z1,z2,z3,z4,z121]),(0,[z0,z1,z2,z3,z4,z667,z5])],[(0,[z0,z114,z1,z2,z3,z4,z137]),(0,[z36,z0,z1,z2,z3,z77,z4]),(0,[z668,z0,z1,z2,z3,z4,z5]),(0,[z0,z669,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z670]),(0,[z46,z0,z389,z2,z3,z4,z5]),(0,[z0,z181,z1,z88,z2,z3,z4]),(0,[z0,z1,z2,z3,z671,z4,z5]),(0,[z0,z1,z2,z98,z3,z93,z5])],[(0,[z0,z1,z2,z3,z4,z5,z672]),(0,[z0,z116,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z673,z3,z4,z5]),(0,[z0,z1,z2,z674,z3,z4,z5]),(0,[z0,z1,z148,z3,z16,z4,z5]),(0,[z0,z675,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z676,z4,z5]),(0,[z0,z1,z2,z19,z3,z4,z139])],[(0,[z0,z424,z1,z160,z2,z3,z5]),(0,[z677,z0,z1,z2,z3,z4,z5]),(0,[z678,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z679,z2,z3,z4,z5])],[(0,[z0,z25,z160,z2,z3,z4,z5]),(0,[z0,z680,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z681,z4,z5]),(0,[z0,z682,z1,z2,z3,z4,z5]),(0,[z38,z0,z1,z2,z3,z4,z37]),(0,[z683,z0,z1,z2,z3,z4,z5]),(0,[z0,z31,z1,z2,z148,z4,z5])],[(0,[z0,z31,z1,z54,z3,z4,z5]),(0,[z38,z0,z48,z1,z2,z3,z4]),(0,[z684,z0,z1,z2,z3,z4,z5])],[(0,[z685,z0,z1,z2,z3,z4,z5]),(0,[z53,z0,z1,z70,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z686,z5]),(0,[z0,z136,z1,z2,z3,z4,z20])]],
   [[(0,[z38,z0,z395,z2,z3,z4,z5])],[(0,[z0,z1,z2,z687,z3,z4,z5]),(0,[z0,z1,z688,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z689]),(0,[z0,z1,z2,z111,z3,z4,z5]),(1,[z0,z395,z2,z3,z4,z5]),(0,[z0,z31,z115,z1,z3,z4,z5]),(0,[z0,z25,z22,z2,z3,z4,z5]),(0,[z0,z1,z690,z2,z3,z4,z5])],[(0,[z0,z691,z1,z2,z3,z4,z5])],[(0,[z0,z692,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z277]),(0,[z0,z693,z1,z2,z3,z4,z5]),(0,[z0,z694,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z695,z4,z5]),(0,[z696,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z697,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z698]),(0,[z0,z1,z2,z3,z4,z699,z5]),(0,[z0,z1,z2,z3,z4,z5,z700])],[(0,[z0,z1,z701,z2,z3,z4,z5]),(0,[z1,z2,z3,z60,z4,z201,z5])],[(0,[z702,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z703]),(0,[z0,z1,z2,z29,z3,z85,z4]),(0,[z704,z0,z1,z2,z3,z4,z5]),(0,[z0,z101,z1,z3,z4,z5,z33]),(0,[z0,z1,z2,z3,z4,z5,z705]),(0,[z0,z1,z2,z3,z4,z5,z20])],[(0,[z0,z181,z1,z2,z3,z4,z137]),(0,[z0,z1,z2,z706,z3,z4,z5])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z124,z159,z160,z2,z3,z5]),(0,[z0,z141,z221,z1,z4,z5]),(0,[z0,z210,z2,z707,z4,z5]),(0,[z0,z1,z708,z3,z4,z5]),(0,[z0,z709,z2,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z710])],[(0,[z1,z2,z106,z711,z4,z5]),(0,[z0,z1,z472,z3,z4,z13]),(0,[z87,z207,z1,z2,z3,z4]),(0,[z0,z115,z40,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z712]),(0,[z0,z1,z2,z93,z5,z713]),(0,[z0,z1,z2,z19,z4,z139]),(0,[z0,z1,z2,z19,z4,z247])],[(0,[z0,z714,z2,z3,z4,z5]),(0,[z584,z1,z70,z3,z4,z5]),(0,[z1,z2,z3,z4,z715,z5]),(0,[z0,z22,z2,z3,z716,z5]),(0,[z0,z717,z1,z2,z3,z4])],[(0,[z0,z1,z718,z2,z3,z4]),(0,[z0,z1,z719,z3,z4,z5]),(0,[z0,z720,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z721]),(0,[z0,z1,z2,z3,z4,z722]),(0,[z0,z59,z1,z2,z5,z34]),(0,[z0,z1,z723,z3,z4,z5]),(0,[z0,z1,z2,z4,z5,z724]),(0,[z0,z22,z2,z3,z5,z26]),(0,[z0,z725,z1,z2,z3,z4]),(0,[z0,z726,z1,z2,z3,z4]),(0,[z0,z1,z2,z727,z4,z5])],[(0,[z0,z159,z1,z2,z3,z5]),(0,[z0,z728,z1,z2,z3,z5]),(0,[z151,z1,z2,z85,z4,z5]),(0,[z1,z2,z3,z60,z729,z5]),(0,[z0,z141,z221,z222,z4,z5]),(0,[z0,z221,z464,z222,z3,z4]),(0,[z0,z94,z1,z3,z170,z5]),(1,[z0,z1,z2,z5,z713])],[(0,[z0,z25,z424,z2,z3,z5]),(0,[z0,z1,z2,z3,z4,z730]),(0,[z0,z1,z2,z3,z4,z731]),(0,[z0,z732,z2,z3,z4,z5]),(0,[z0,z1,z105,z66,z4,z5]),(0,[z0,z1,z2,z733,z3,z4]),(0,[z0,z1,z734,z2,z3,z4]),(0,[z0,z1,z2,z735,z4,z5]),(0,[z0,z736,z1,z2,z4,z5])],[(0,[z0,z1,z2,z3,z4,z737]),(0,[z0,z1,z2,z3,z4,z738]),(0,[z0,z739,z1,z3,z4,z5]),(0,[z0,z94,z1,z106,z4,z5]),(0,[z0,z25,z78,z2,z3,z5]),(0,[z0,z389,z472,z3,z4,z5]),(1,[z0,z2,z707,z4,z5]),(0,[z0,z1,z233,z3,z198,z4]),(0,[z0,z1,z105,z148,z4,z5])]],
   [[(0,[z0,z442,z88,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z740]),(0,[z0,z101,z1,z5,z229,z33]),(0,[z0,z1,z2,z3,z4,z741])],[(0,[z0,z1,z2,z742,z4,z5]),(0,[z0,z1,z105,z341,z4,z5]),(0,[z0,z1,z3,z727,z4,z5])],[(0,[z743,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z744]),(0,[z36,z0,z2,z3,z154,z4]),(0,[z0,z1,z2,z5,z713,z34])],[(0,[z44,z76,z2,z3,z4,z5]),(0,[z0,z1,z2,z745,z4,z5]),(0,[z0,z1,z2,z3,z746,z4]),(0,[z87,z1,z2,z3,z4,z37]),(0,[z0,z1,z164,z2,z3,z4]),(0,[z0,z1,z3,z4,z5,z747]),(0,[z0,z1,z105,z727,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z748]),(0,[z0,z1,z2,z749,z4,z5]),(0,[z0,z1,z88,z273,z3,z4]),(0,[z0,z1,z750,z3,z4,z5])],[(0,[z0,z1,z2,z3,z751,z5]),(0,[z0,z752,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z753]),(1,[z0,z1,z727,z4,z5]),(0,[z0,z754,z2,z3,z4,z5])],[(0,[z0,z94,z1,z3,z5,z33])],[(0,[z0,z1,z2,z3,z4,z755]),(0,[z0,z31,z263,z1,z4,z5]),(0,[z0,z199,z1,z2,z5,z34]),(0,[z0,z756,z1,z2,z3,z20])]],
   [[(0,[z0,z1,z2,z3,z4,z277]),(0,[z0,z1,z220,z3,z4,z5]),(0,[z0,z757,z2,z3,z4,z5]),(0,[z0,z460,z1,z3,z5,z33]),(0,[z53,z1,z54,z35,z4,z5]),(0,[z0,z1,z758,z2,z3,z4]),(1,[z1,z2,z711,z4,z5]),(0,[z151,z1,z2,z711,z4,z5]),(0,[z21,z1,z2,z3,z60,z5]),(0,[z0,z1,z2,z3,z4,z759])],[(0,[z0,z2,z3,z716,z5,z26]),(0,[z0,z2,z3,z77,z760,z4]),(1,[z0,z1,z3,z4,z741]),(0,[z0,z1,z761,z3,z4,z5]),(0,[z0,z117,z1,z2,z155,z4])],[(0,[z0,z1,z2,z762,z4,z5]),(0,[z483,z1,z2,z106,z4,z5]),(0,[z0,z1,z2,z3,z763,z4]),(0,[z0,z181,z2,z3,z4,z137]),(0,[z0,z2,z3,z760,z4,z137]),(0,[z0,z199,z1,z16,z4,z5])],[(0,[z0,z1,z764,z3,z4,z5]),(0,[z44,z765,z2,z3,z4,z5]),(0,[z0,z1,z2,z306,z4,z5]),(0,[z0,z766,z1,z2,z3,z4]),(0,[z0,z1,z767,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z768]),(0,[z0,z769,z2,z3,z4,z5]),(0,[z0,z1,z2,z770,z4,z5]),(0,[z0,z1,z771,z3,z4,z5]),(0,[z0,z181,z271,z2,z3,z4]),(0,[z0,z772,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z773,z4,z5]),(0,[z0,z221,z164,z222,z3,z4]),(0,[z0,z774,z2,z3,z4,z5])],[(0,[z142,z160,z2,z3,z4,z5]),(0,[z0,z1,z3,z775,z4,z5]),(0,[z0,z424,z1,z2,z3,z730]),(0,[z0,z442,z2,z3,z4,z137]),(0,[z0,z1,z2,z4,z5,z776]),(0,[z0,z777,z1,z2,z3,z4]),(0,[z0,z1,z778,z3,z4,z5]),(0,[z779,z1,z2,z3,z4,z5]),(0,[z0,z1,z780,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z108]),(0,[z0,z2,z3,z781,z4,z5]),(0,[z0,z114,z1,z2,z3,z572])],[(0,[z0,z1,z2,z3,z782,z5]),(0,[z0,z1,z3,z783,z4,z5]),(0,[z0,z117,z1,z2,z477,z4])],[(0,[z38,z1,z690,z2,z3,z4]),(0,[z0,z31,z1,z468,z4,z5]),(0,[z0,z1,z2,z784,z4,z5]),(0,[z0,z1,z785,z3,z4,z5]),(0,[z0,z117,z1,z2,z4,z786])]],
   [[(0,[z0,z787,z222,z3,z4,z5]),(0,[z0,z1,z2,z4,z5,z788]),(0,[z0,z1,z2,z4,z786,z118]),(0,[z0,z136,z114,z1,z2,z3])],[(0,[z0,z1,z3,z4,z5,z789])],[(0,[z0,z1,z472,z47,z4,z5]),(0,[z0,z1,z790,z3,z4,z5]),(0,[z0,z141,z1,z164,z2,z4]),(0,[z0,z40,z787,z3,z4,z5]),(0,[z0,z1,z148,z4,z5,z593])],[(0,[z124,z765,z2,z3,z4,z5]),(0,[z1,z719,z2,z3,z4,z5]),(0,[z0,z791,z2,z3,z4,z5]),(0,[z0,z1,z220,z106,z4,z5]),(0,[z792,z1,z2,z3,z4,z5]),(0,[z0,z1,z89,z3,z198,z4]),(0,[z793,z0,z1,z2,z3,z4])]],
   [[(0,[z0,z1,z2,z794,z3,z4]),(0,[z0,z795,z1,z2,z3,z5]),(0,[z0,z796,z1,z2,z3,z4]),(0,[z0,z1,z797,z3,z4,z5]),(0,[z0,z442,z2,z3,z77,z4]),(0,[z0,z2,z707,z90,z4,z5]),(0,[z1,z2,z3,z4,z5,z798]),(0,[z0,z1,z2,z799,z4,z5])],[(0,[z124,z160,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z800]),(0,[z585,z1,z54,z3,z4,z5]),(0,[z0,z1,z464,z2,z519,z4]),(0,[z0,z1,z801,z2,z3,z4]),(0,[z0,z22,z2,z3,z362,z26]),(0,[z0,z199,z1,z2,z4,z5]),(0,[z802,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z4,z139,z786])],[(0,[z0,z1,z803,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z804]),(0,[z0,z1,z805,z2,z3,z4]),(0,[z46,z1,z86,z3,z201,z5]),(0,[z0,z1,z2,z3,z806,z4]),(0,[z0,z25,z2,z3,z138,z5])],[(0,[z0,z807,z1,z2,z3,z4]),(0,[z0,z1,z2,z808,z4,z5]),(0,[z0,z1,z2,z3,z4,z809]),(0,[z483,z1,z54,z3,z4,z5]),(0,[z0,z210,z2,z162,z4,z5]),(0,[z810,z1,z2,z3,z4,z5]),(0,[z0,z372,z2,z3,z4,z137]),(0,[z0,z811,z2,z3,z4,z5])]],
   [[(0,[z0,z395,z2,z3,z4,z5]),(0,[z0,z812,z2,z3,z4,z5]),(0,[z0,z48,z1,z23,z3,z4]),(0,[z813,z1,z2,z3,z4,z5]),(0,[z0,z181,z343,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z17]),(0,[z0,z48,z1,z3,z4,z741])],[(0,[z0,z1,z814,z2,z3,z5]),(0,[z0,z1,z2,z3,z815,z5]),(0,[z0,z221,z222,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z816]),(0,[z0,z1,z2,z3,z143,z817]),(0,[z0,z1,z2,z3,z182,z20])],[(0,[z0,z818,z1,z3,z4,z5]),(0,[z87,z1,z2,z3,z4,z715]),(0,[z0,z1,z2,z3,z4,z819])],[(0,[z0,z1,z2,z3,z4,z820]),(0,[z0,z78,z472,z3,z4,z5])]],
   [[(0,[z74,z160,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z821]),(1,[z1,z719,z3,z4,z5]),(0,[z0,z1,z2,z3,z822,z4]),(0,[z0,z1,z2,z3,z4,z823]),(0,[z84,z1,z2,z711,z4,z5]),(0,[z0,z824,z1,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z825]),(0,[z0,z1,z826,z3,z4,z5]),(0,[z0,z1,z2,z827,z3,z4]),(0,[z0,z31,z1,z514,z4,z5])],[(0,[z0,z828,z1,z2,z3,z4]),(0,[z0,z1,z829,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z830])],[(0,[z0,z1,z2,z3,z4,z5]),(0,[z440,z0,z2,z3,z77,z4]),(0,[z0,z1,z2,z3,z4,z831]),(0,[z0,z1,z2,z357,z4,z5]),(0,[z36,z0,z2,z3,z550,z4]),(0,[z0,z2,z3,z707,z4,z5]),(0,[z0,z210,z2,z303,z4,z5]),(0,[z0,z2,z3,z138,z716,z5]),(0,[z0,z199,z1,z2,z170,z5]),(0,[z0,z1,z2,z3,z4,z563]),(0,[z0,z1,z2,z4,z5,z786])],[(0,[z0,z1,z2,z3,z832,z5]),(1,[z1,z2,z3,z729,z5]),(0,[z0,z833,z1,z3,z4,z5]),(0,[z0,z1,z2,z19,z535,z4]),(1,[z0,z787,z3,z4,z5]),(0,[z0,z1,z2,z4,z5,z834]),(0,[z1,z2,z3,z4,z5,z835])]],
   [[(0,[z0,z424,z2,z3,z5,z26]),(0,[z0,z1,z2,z3,z4,z836]),(0,[z44,z76,z2,z3,z253,z4]),(0,[z0,z1,z2,z3,z4,z13]),(0,[z0,z1,z2,z357,z4,z13]),(0,[z0,z1,z2,z3,z4,z837])],[(0,[z0,z838,z1,z2,z4,z5]),(0,[z0,z31,z1,z189,z4,z5]),(0,[z0,z2,z3,z4,z5,z839]),(0,[z0,z1,z2,z3,z579,z20]),(0,[z0,z48,z442,z2,z3,z4]),(0,[z840,z1,z2,z3,z4,z5]),(0,[z0,z116,z2,z233,z90,z4]),(0,[z0,z116,z279,z2,z4,z5]),(0,[z0,z1,z2,z3,z143,z5]),(0,[z0,z1,z2,z706,z93,z5])],[(0,[z0,z1,z2,z3,z5,z841]),(0,[z0,z1,z2,z3,z842,z4]),(0,[z0,z1,z2,z29,z3,z4]),(0,[z0,z843,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z844]),(0,[z0,z1,z2,z3,z4,z845]),(0,[z0,z846,z1,z3,z4,z5]),(0,[z0,z31,z1,z32,z4,z5]),(0,[z0,z101,z1,z3,z5,z710])],[(0,[z0,z1,z2,z3,z847,z4]),(0,[z548,z76,z2,z3,z4,z5]),(0,[z0,z120,z1,z2,z3,z4])]],
   [[(0,[z0,z765,z2,z3,z4,z5]),(0,[z0,z1,z848,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z849]),(0,[z0,z1,z164,z2,z519,z4]),(0,[z0,z1,z148,z320,z4,z5]),(0,[z0,z48,z1,z407,z3,z4])],[(0,[z0,z1,z850,z3,z4,z5]),(0,[z0,z1,z851,z3,z4,z5]),(0,[z0,z1,z472,z3,z4,z121]),(0,[z46,z1,z2,z3,z729,z5]),(0,[z0,z1,z88,z3,z132,z4])],[(0,[z0,z389,z2,z3,z4,z5]),(0,[z0,z31,z1,z681,z4,z5]),(0,[z0,z389,z2,z357,z4,z5]),(0,[z0,z1,z2,z3,z760,z4]),(0,[z0,z2,z3,z4,z5,z852]),(0,[z0,z853,z2,z3,z4,z5])],[(0,[z0,z854,z2,z3,z4,z5]),(0,[z0,z855,z1,z2,z3,z4])]],
   [[(0,[z0,z1,z856,z3,z4,z5]),(0,[z0,z1,z2,z857,z4,z5]),(0,[z124,z424,z160,z2,z3,z5]),(0,[z44,z76,z2,z3,z4,z45]),(0,[z0,z1,z2,z3,z858,z4]),(0,[z0,z1,z2,z85,z170,z5]),(0,[z0,z101,z1,z3,z170,z5]),(0,[z0,z1,z859,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z860]),(0,[z0,z1,z2,z3,z4,z861]),(0,[z0,z1,z862,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z863]),(0,[z0,z1,z2,z3,z4,z864]),(0,[z0,z442,z2,z19,z3,z4]),(0,[z0,z116,z352,z1,z4,z5]),(0,[z0,z865,z1,z3,z4,z5])],[(0,[z0,z866,z2,z3,z4,z5]),(0,[z151,z67,z1,z2,z85,z4]),(0,[z0,z867,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z868]),(0,[z869,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z870]),(0,[z871,z1,z2,z3,z4,z5]),(0,[z0,z31,z1,z32,z170,z5])]],
   [[(0,[z0,z872,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z715]),(0,[z0,z352,z210,z1,z4,z5])],[(0,[z0,z1,z2,z873,z4,z5]),(0,[z0,z874,z2,z3,z4,z5]),(0,[z0,z2,z3,z760,z4,z5]),(0,[z0,z48,z1,z3,z4,z82]),(0,[z0,z756,z1,z2,z3,z182])],[(0,[z0,z1,z875,z3,z4,z5]),(0,[z1,z2,z3,z4,z715,z37]),(0,[z0,z1,z3,z198,z4,z5]),(0,[z0,z199,z101,z1,z4,z5]),(0,[z0,z92,z1,z2,z5,z713])],[(0,[z0,z1,z70,z3,z170,z5]),(0,[z46,z1,z2,z3,z201,z13]),(0,[z0,z1,z2,z876,z4,z5]),(0,[z0,z181,z2,z3,z4,z565]),(0,[z0,z1,z2,z877,z4,z5]),(0,[z0,z1,z3,z4,z5,z741])]],
   [[(0,[z0,z442,z2,z3,z4,z5]),(0,[z0,z1,z2,z878,z4,z5]),(0,[z0,z879,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z880]),(0,[z0,z1,z2,z98,z93,z5]),(0,[z0,z1,z2,z98,z93,z563])],[(0,[z0,z422,z2,z3,z77,z4]),(0,[z87,z1,z2,z3,z415,z4]),(0,[z0,z352,z1,z3,z4,z5]),(0,[z0,z101,z1,z3,z5,z33]),(0,[z0,z68,z1,z58,z3,z16])],[(0,[z0,z1,z2,z3,z881,z5]),(0,[z0,z94,z1,z85,z4,z5]),(0,[z0,z1,z2,z882,z3,z4]),(0,[z84,z1,z111,z106,z4,z5]),(0,[z0,z22,z78,z2,z3,z5]),(0,[z0,z1,z2,z3,z883,z5]),(0,[z0,z1,z2,z707,z4,z5]),(0,[z0,z92,z1,z2,z5,z34])],[(0,[z0,z884,z2,z3,z4,z5]),(0,[z0,z2,z3,z885,z4,z5]),(0,[z53,z1,z54,z306,z4,z5]),(0,[z0,z1,z2,z3,z4,z886]),(0,[z0,z1,z887,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z888]),(0,[z0,z1,z2,z4,z5,z229]),(0,[z0,z1,z88,z3,z4,z741])]],
   [[(0,[z0,z1,z889,z2,z3,z4]),(0,[z0,z1,z890,z3,z4,z5])],[(0,[z0,z1,z2,z891,z4,z5]),(0,[z0,z1,z892,z3,z4,z5]),(0,[z46,z389,z2,z3,z201,z5]),(0,[z0,z893,z2,z3,z4,z5])],[(0,[z0,z894,z1,z2,z4,z5]),(0,[z0,z1,z895,z3,z4,z5]),(0,[z0,z896,z1,z2,z3,z4])],[(0,[z0,z1,z2,z897,z4,z5]),(0,[z76,z765,z2,z3,z4,z5]),(0,[z0,z1,z2,z898,z4,z5]),(0,[z0,z1,z2,z899,z4,z5]),(0,[z0,z1,z2,z900,z4,z5]),(0,[z0,z199,z1,z54,z4,z5]),(0,[z0,z1,z2,z4,z5,z901]),(0,[z0,z1,z2,z3,z4,z786])]],
   [[(0,[z0,z424,z1,z2,z3,z746]),(0,[z0,z1,z2,z3,z4,z902]),(0,[z9,z1,z2,z3,z4,z37]),(0,[z0,z115,z3,z636,z4,z5]),(0,[z0,z903,z1,z2,z3,z4]),(0,[z0,z1,z2,z19,z624,z4]),(0,[z0,z1,z105,z4,z5,z225])],[(0,[z0,z1,z2,z47,z4,z5]),(0,[z0,z22,z2,z3,z251,z26]),(1,[z0,z756,z1,z2,z3])],[(0,[z0,z1,z3,z904,z4,z5]),(0,[z0,z1,z2,z3,z4,z905]),(0,[z0,z906,z1,z3,z4,z5]),(0,[z0,z92,z1,z5,z108,z34])],[(0,[z0,z1,z2,z3,z253,z4]),(0,[z0,z907,z2,z3,z4,z5]),(0,[z0,z1,z2,z47,z4,z13]),(0,[z0,z1,z908,z2,z3,z4]),(1,[z0,z2,z3,z716,z5]),(0,[z0,z1,z727,z32,z4,z5]),(0,[z0,z31,z619,z1,z4,z5]),(0,[z0,z2,z3,z4,z5,z909])]],
   [[(0,[z1,z2,z3,z711,z4,z5]),(0,[z0,z117,z442,z2,z3,z4]),(0,[z548,z1,z2,z3,z4,z39])],[(0,[z0,z1,z910,z3,z4,z5]),(0,[z87,z325,z1,z2,z3,z4]),(0,[z1,z2,z3,z4,z39,z715])],[(0,[z196,z120,z1,z70,z3,z4]),(0,[z0,z1,z2,z911,z3,z4])],[(0,[z0,z912,z2,z3,z4,z5]),(0,[z0,z1,z54,z3,z170,z5]),(0,[z0,z1,z913,z3,z4,z5]),(0,[z388,z1,z2,z106,z4,z5]),(0,[z0,z25,z169,z2,z3,z5]),(0,[z0,z1,z2,z3,z914,z5])]],
   [[(0,[z0,z1,z2,z915,z4,z5]),(0,[z0,z916,z1,z3,z4,z5]),(0,[z0,z199,z101,z1,z5,z33]),(0,[z0,z92,z94,z1,z5,z34])],[(0,[z0,z1,z2,z3,z4,z917]),(0,[z0,z76,z2,z3,z4,z45]),(0,[z196,z1,z719,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z918]),(0,[z0,z389,z2,z47,z4,z5]),(0,[z0,z1,z2,z3,z729,z5]),(0,[z0,z1,z2,z3,z919,z4]),(0,[z0,z136,z756,z1,z2,z3])],[(0,[z0,z78,z2,z3,z4,z5]),(0,[z0,z78,z2,z357,z4,z5]),(0,[z46,z641,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z4,z45]),(0,[z0,z1,z2,z3,z4,z920]),(0,[z0,z921,z1,z2,z4,z5]),(0,[z922,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z923,z3,z4,z5]),(0,[z44,z76,z2,z3,z4,z150]),(0,[z0,z1,z86,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z924]),(0,[z0,z78,z2,z3,z4,z13]),(0,[z0,z1,z86,z357,z4,z5]),(0,[z0,z31,z1,z613,z4,z5])],[(1,[z765,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z5,z925]),(0,[z38,z1,z2,z353,z3,z4]),(0,[z0,z1,z58,z3,z16,z17]),(0,[z0,z114,z1,z2,z3,z610])],[(0,[z0,z1,z2,z3,z926,z4]),(0,[z0,z1,z2,z3,z4,z927]),(0,[z0,z1,z2,z3,z928,z4]),(0,[z53,z1,z54,z3,z4,z5]),(0,[z0,z1,z220,z85,z4,z5]),(0,[z0,z1,z86,z3,z4,z13]),(0,[z0,z1,z929,z3,z4,z5]),(0,[z0,z1,z3,z16,z5,z710])],[(0,[z0,z1,z2,z930,z4,z5]),(0,[z0,z442,z2,z3,z4,z39]),(0,[z0,z25,z2,z3,z716,z5]),(0,[z0,z1,z3,z4,z741,z82])]],
   [[(0,[z0,z1,z2,z931,z4,z5]),(0,[z84,z1,z220,z106,z4,z5]),(0,[z46,z1,z2,z47,z201,z5]),(0,[z0,z31,z1,z300,z4,z5]),(0,[z932,z1,z2,z3,z4,z5]),(0,[z0,z31,z625,z1,z4,z5]),(0,[z0,z1,z2,z233,z3,z4])],[(0,[z0,z933,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z934,z5]),(0,[z46,z1,z472,z3,z201,z5]),(0,[z1,z2,z3,z4,z5,z935]),(0,[z0,z1,z2,z936,z4,z5]),(0,[z0,z92,z1,z2,z170,z5]),(0,[z0,z726,z1,z2,z3,z143]),(0,[z0,z1,z2,z3,z937,z5]),(0,[z0,z199,z1,z2,z93,z5]),(0,[z0,z1,z2,z938,z4,z5]),(0,[z0,z1,z270,z3,z16,z5])],[(0,[z765,z160,z2,z3,z4,z5]),(0,[z0,z939,z2,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z940]),(0,[z38,z1,z2,z3,z4,z203]),(0,[z0,z561,z114,z1,z2,z3]),(0,[z0,z1,z2,z941,z4,z5]),(0,[z36,z0,z2,z3,z760,z4])],[(0,[z0,z160,z2,z3,z4,z45]),(0,[z0,z181,z2,z3,z4,z670]),(0,[z0,z1,z2,z942,z4,z5]),(0,[z0,z1,z2,z3,z4,z943]),(0,[z0,z944,z1,z2,z3,z4]),(0,[z0,z1,z148,z727,z4,z5]),(0,[z0,z1,z58,z3,z16,z5])]],
   [[(0,[z0,z945,z1,z2,z3,z5]),(0,[z0,z31,z1,z631,z4,z5]),(0,[z0,z1,z2,z3,z4,z121]),(0,[z0,z389,z86,z3,z4,z5]),(0,[z0,z1,z2,z357,z4,z121]),(0,[z0,z1,z2,z3,z362,z4]),(0,[z0,z1,z3,z16,z170,z5])],[(0,[z0,z1,z946,z3,z4,z5]),(0,[z0,z1,z2,z3,z947,z5]),(0,[z683,z76,z2,z3,z4,z5]),(0,[z0,z948,z1,z2,z3,z4]),(0,[z0,z117,z1,z2,z152,z4]),(1,[z1,z2,z3,z4,z715]),(0,[z0,z1,z2,z3,z185,z20])],[(0,[z53,z1,z719,z3,z4,z5]),(0,[z171,z1,z2,z85,z4,z5]),(0,[z0,z949,z2,z3,z4,z5]),(0,[z21,z576,z1,z2,z3,z5]),(0,[z0,z1,z2,z519,z4,z5]),(0,[z0,z1,z950,z2,z3,z4]),(0,[z0,z1,z3,z951,z4,z5]),(0,[z0,z1,z2,z3,z4,z952]),(0,[z0,z92,z94,z1,z4,z5])],[(0,[z0,z1,z2,z953,z4,z5]),(0,[z0,z954,z1,z2,z4,z5]),(0,[z0,z116,z89,z2,z90,z4]),(0,[z0,z1,z2,z3,z5,z713])]],
   [[(0,[z1,z765,z2,z3,z4,z5]),(0,[z0,z1,z70,z306,z4,z5]),(0,[z0,z1,z2,z955,z4,z5]),(0,[z0,z1,z956,z3,z4,z5]),(0,[z0,z1,z2,z957,z3,z4]),(0,[z0,z1,z58,z3,z5,z710])],[(0,[z0,z1,z2,z4,z958,z5]),(0,[z0,z1,z2,z3,z4,z959]),(0,[z46,z78,z2,z3,z201,z5]),(0,[z0,z1,z2,z960,z4,z5]),(0,[z0,z116,z2,z707,z4,z5]),(0,[z0,z1,z961,z2,z3,z4]),(0,[z0,z1,z2,z93,z170,z5])],[(0,[z0,z1,z787,z3,z4,z5]),(0,[z0,z1,z2,z3,z962,z5]),(0,[z0,z1,z2,z93,z5,z239]),(0,[z0,z1,z2,z963,z4,z5])],[(0,[z0,z1,z2,z3,z4,z964]),(0,[z0,z1,z517,z148,z4,z5]),(0,[z1,z2,z3,z729,z201,z5]),(0,[z0,z141,z1,z464,z2,z4]),(0,[z0,z352,z1,z89,z3,z4])]],
   [[(0,[z0,z181,z2,z3,z4,z277]),(0,[z0,z389,z2,z3,z4,z121]),(0,[z0,z1,z2,z965,z3,z4]),(0,[z0,z1,z2,z3,z966,z5])],[(0,[z0,z1,z967,z2,z3,z4]),(0,[z0,z1,z968,z2,z3,z5]),(0,[z0,z1,z969,z2,z3,z4]),(0,[z0,z970,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z971]),(0,[z123,z1,z2,z3,z4,z39]),(0,[z0,z1,z88,z653,z3,z4])],[(0,[z0,z1,z2,z972,z3,z4]),(0,[z0,z424,z78,z2,z3,z5]),(0,[z0,z1,z3,z4,z5,z973]),(0,[z0,z1,z2,z3,z974,z5]),(0,[z0,z1,z2,z3,z444,z20]),(0,[z0,z1,z975,z3,z4,z5]),(0,[z0,z1,z2,z3,z65,z20]),(0,[z0,z114,z756,z1,z2,z3])],[(0,[z0,z442,z2,z3,z4,z277]),(0,[z0,z976,z2,z3,z4,z5]),(0,[z38,z1,z2,z3,z4,z715]),(0,[z0,z756,z1,z2,z3,z4])]],
   [[(0,[z1,z719,z70,z3,z4,z5]),(0,[z1,z2,z711,z85,z4,z5]),(0,[z0,z221,z787,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z977])],[(0,[z0,z978,z1,z2,z3,z4]),(0,[z0,z1,z2,z979,z4,z5]),(0,[z0,z221,z519,z222,z4,z5]),(0,[z0,z1,z3,z4,z5,z980]),(0,[z0,z1,z981,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z817]),(0,[z0,z1,z2,z3,z4,z982]),(0,[z0,z1,z88,z3,z110,z4])],[(0,[z38,z395,z2,z3,z4,z39]),(0,[z0,z356,z1,z2,z98,z93])],[(0,[z46,z1,z2,z3,z201,z121]),(0,[z0,z352,z1,z233,z3,z4]),(0,[z0,z114,z97,z1,z2,z3]),(0,[z0,z94,z1,z93,z4,z5])]],
   [[(0,[z0,z1,z69,z2,z3,z4]),(0,[z0,z1,z2,z983,z4,z5])],[(0,[z0,z1,z2,z3,z984,z5]),(0,[z0,z1,z2,z3,z4,z985]),(0,[z0,z78,z2,z47,z4,z5]),(0,[z0,z986,z1,z2,z3,z4]),(0,[z987,z1,z2,z3,z4,z5]),(0,[z0,z988,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z989,z4]),(0,[z0,z1,z3,z5,z710,z33]),(0,[z0,z756,z1,z2,z3,z5])],[(0,[z84,z1,z2,z106,z4,z5]),(0,[z990,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z991]),(0,[z0,z1,z2,z3,z992,z4]),(0,[z0,z1,z2,z4,z5,z713])],[(0,[z0,z1,z2,z3,z4,z150]),(0,[z0,z993,z1,z2,z3,z5]),(0,[z0,z1,z86,z47,z4,z5]),(0,[z657,z1,z2,z3,z4,z37]),(0,[z0,z1,z2,z3,z994,z4]),(0,[z0,z1,z2,z3,z4,z995])]],
   [[(0,[z0,z1,z2,z3,z4,z996]),(0,[z0,z1,z2,z35,z4,z5]),(0,[z0,z1,z54,z306,z4,z5]),(0,[z38,z1,z2,z3,z4,z39])],[(0,[z0,z997,z2,z3,z4,z5]),(0,[z0,z998,z2,z3,z4,z5]),(0,[z0,z999,z2,z3,z4,z5]),(0,[z0,z116,z2,z90,z4,z5]),(0,[z1000,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z1001,z4,z5]),(0,[z1,z2,z3,z4,z729,z5]),(0,[z0,z1,z2,z3,z4,z251]),(0,[z0,z31,z1,z32,z143,z5])],[(0,[z0,z1002,z2,z3,z4,z5]),(0,[z0,z1,z1003,z3,z4,z5]),(0,[z0,z221,z279,z3,z4,z5])]],
   [[(0,[z0,z1004,z2,z3,z4,z5]),(0,[z0,z442,z2,z3,z4,z37]),(0,[z0,z1,z2,z3,z5,z710])],[(0,[z0,z1,z2,z1005,z4,z5]),(0,[z0,z1006,z2,z3,z4,z5]),(0,[z0,z389,z2,z3,z4,z13]),(1,[z0,z1,z2,z4,z786])],[(0,[z151,z1,z2,z29,z85,z4]),(0,[z0,z1,z2,z3,z4,z1007]),(0,[z0,z1,z2,z98,z697,z5]),(0,[z1008,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z4,z5,z1009]),(0,[z0,z1,z2,z3,z4,z1010])],[(0,[z0,z1,z2,z3,z1011,z5]),(0,[z0,z1,z2,z711,z4,z5]),(0,[z0,z67,z1,z2,z3,z4]),(0,[z0,z1,z2,z47,z4,z121]),(0,[z1012,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1013]),(0,[z0,z1,z3,z4,z5,z1014]),(0,[z0,z1,z2,z3,z4,z1015]),(0,[z0,z356,z1,z2,z3,z4])]],
   [[(0,[z0,z78,z86,z3,z4,z5]),(0,[z0,z116,z352,z90,z4,z5]),(0,[z0,z1016,z1,z2,z4,z5])],[(0,[z0,z141,z115,z1,z4,z5]),(0,[z36,z0,z2,z3,z77,z4])],[(0,[z0,z199,z1,z70,z4,z5]),(0,[z0,z1,z2,z3,z1017,z4]),(0,[z0,z1,z1018,z2,z3,z4]),(0,[z0,z1,z2,z3,z170,z5]),(0,[z0,z1,z3,z16,z5,z157]),(0,[z0,z1,z2,z98,z5,z713])],[(0,[z0,z1,z2,z1019,z4,z5]),(0,[z0,z2,z3,z77,z4,z277]),(0,[z0,z1,z2,z3,z4,z1020]),(0,[z0,z1,z2,z3,z1021,z5]),(0,[z0,z181,z2,z3,z4,z203]),(0,[z1022,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z1023,z2,z3,z4]),(0,[z196,z1,z70,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1024]),(0,[z0,z1,z2,z3,z4,z1025]),(0,[z0,z31,z1,z16,z93,z5])],[(0,[z0,z1,z2,z3,z4,z1026]),(0,[z44,z76,z2,z3,z4,z277]),(0,[z427,z1,z2,z85,z4,z5]),(0,[z0,z1,z2,z3,z1027,z5]),(1,[z0,z1,z3,z5,z710]),(0,[z0,z1,z3,z132,z4,z741])],[(0,[z0,z1028,z1,z3,z4,z5]),(0,[z206,z1,z70,z3,z4,z5]),(0,[z0,z115,z787,z3,z4,z5]),(0,[z0,z1,z2,z1029,z4,z5]),(0,[z0,z1,z2,z3,z716,z5]),(0,[z1030,z1,z2,z3,z4,z5]),(0,[z0,z31,z1,z404,z4,z5])],[(0,[z0,z1,z2,z3,z4,z1031]),(0,[z0,z1,z2,z3,z4,z1032]),(0,[z0,z1,z2,z3,z4,z1033]),(0,[z0,z141,z1,z2,z4,z5])]],
   [[(0,[z0,z424,z1,z2,z3,z5]),(0,[z0,z1,z2,z4,z5,z1034]),(0,[z0,z1,z1035,z3,z4,z5]),(0,[z0,z1,z1036,z3,z4,z5]),(0,[z46,z1,z2,z3,z201,z5]),(0,[z0,z78,z2,z3,z4,z121]),(0,[z46,z1,z2,z357,z201,z5]),(0,[z21,z1,z2,z3,z729,z5]),(0,[z0,z1037,z1,z2,z4,z5]),(0,[z1038,z1,z2,z3,z4,z5])],[(0,[z0,z1039,z2,z3,z4,z5]),(0,[z0,z1,z58,z3,z601,z5])],[(0,[z0,z1,z2,z3,z4,z1040]),(0,[z0,z1,z111,z3,z4,z5]),(0,[z0,z1,z2,z1041,z4,z5]),(0,[z0,z1,z2,z1042,z4,z5]),(0,[z0,z1,z86,z3,z4,z121]),(0,[z38,z442,z2,z3,z4,z39]),(0,[z0,z1,z2,z1043,z4,z5]),(0,[z0,z181,z2,z3,z760,z4]),(0,[z0,z611,z2,z3,z77,z4]),(0,[z0,z68,z1,z2,z3,z4]),(0,[z0,z1,z2,z1044,z4,z5]),(0,[z0,z94,z1,z3,z16,z5])],[(0,[z0,z1,z1045,z3,z4,z5]),(0,[z0,z116,z198,z90,z4,z5]),(0,[z1046,z1,z2,z3,z4,z5]),(1,[z0,z2,z3,z760,z4]),(0,[z0,z1047,z2,z3,z4,z5]),(0,[z0,z117,z1,z2,z4,z118])]],
   [[(0,[z0,z1048,z1,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z1049]),(0,[z0,z1,z464,z2,z3,z4]),(0,[z0,z2,z3,z716,z4,z5]),(0,[z36,z0,z2,z436,z3,z4]),(0,[z0,z1050,z1,z2,z3,z4]),(0,[z0,z94,z1,z3,z4,z5]),(0,[z0,z31,z1,z102,z4,z5]),(0,[z0,z1051,z1,z3,z4,z5])],[(0,[z0,z1,z2,z3,z1052,z5]),(0,[z0,z1,z2,z106,z170,z5]),(0,[z0,z1,z1053,z3,z4,z5]),(0,[z0,z48,z1,z617,z3,z4])],[(0,[z0,z1,z2,z3,z1054,z5]),(0,[z0,z1,z2,z3,z1055,z5]),(0,[z0,z1056,z2,z3,z4,z5]),(0,[z0,z2,z787,z3,z4,z5]),(0,[z0,z1,z89,z2,z3,z4]),(0,[z0,z2,z162,z707,z4,z5]),(0,[z0,z31,z1,z727,z4,z5]),(0,[z0,z1057,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z1058]),(0,[z0,z1,z2,z19,z4,z786])],[(0,[z0,z1,z1059,z3,z4,z5]),(0,[z0,z25,z2,z3,z378,z5]),(0,[z0,z1,z472,z3,z4,z5]),(0,[z196,z1,z69,z70,z3,z4]),(0,[z1,z54,z719,z3,z4,z5]),(0,[z0,z1,z472,z357,z4,z5])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 556) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 556).take 478) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1034)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [556, 478] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_nil pbend))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 93).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 93).take 35).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 128)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [93, 35] = true :=
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

end PEqualNP.Outside.L_meta_40752

theorem PEqualNP.Outside.L_meta_40752 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808384 * 2 ^ 32 + 4272603264) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808384 * 2 ^ 32 + 4272603264) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_40752.solve