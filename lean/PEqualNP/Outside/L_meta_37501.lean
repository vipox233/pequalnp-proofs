import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_37501

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
  Nat.testBit (4276809448 * 2 ^ 32 + 4276808904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x6800106340893910#64 ++ 0x8680010634089391#64 ++ 0xf404f4e7c19f793f#64 ++ 0x7f404f4e7c19f793#64 : BitVec 256),
   (0x1009410882240269#64 ++ 0x0100941088224026#64 ++ 0xef1b4b18c6648ffe#64 ++ 0xfef1b4b18c6648ff#64 : BitVec 256),
   (0x20628c151858d180#64 ++ 0x120628c151858d18#64 ++ 0xdee38c1f3878f1cd#64 ++ 0xedee38c1f3878f1c#64 : BitVec 256),
   (0x40b40ea02d80ec02#64 ++ 0x240b40ea02d80ec0#64 ++ 0xbffc0fe03f80fe0b#64 ++ 0xdbffc0fe03f80fe0#64 : BitVec 256),
   (0x80dfe0003776000c#64 ++ 0x380dfe0003776000#64 ++ 0x7cfff0003fff0007#64 ++ 0xc7cfff0003fff000#64 : BitVec 256),
   (0x01ffffdec000000f#64 ++ 0xc01ffffdec000000#64 ++ 0xfdffffffc0000000#64 ++ 0x3fdffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [1, 4]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [7, 5]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [10, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [11, 12]⟩, ⟨.and, [8, 6]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x01f6bed640000006 0xc01f6bed64000000 0xbdfcbfe700000000 0x1bdfcbfe70000000

def z1 : W := mkw 0x1009410882240269 0x0100941088224026 0xef1b4b18c6648ffe 0xfef1b4b18c6648ff

def z2 : W := mkw 0x20628c151858d180 0x120628c151858d18 0xdee38c1f3878f1cd 0xedee38c1f3878f1c

def z3 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0xbffc0fe03f80fe0b 0xdbffc0fe03f80fe0

def z4 : W := mkw 0x6800106340893910 0x8680010634089391 0xf404f4e7c19f793f 0x7f404f4e7c19f793

def z5 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0x7cfff0003fff0007 0xc7cfff0003fff000

def z6 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xfdffffffc0000000 0x3fdffffffc000000

def z7 : W := mkw 0x80d6a00035520004 0x380d6a0003552000 0x3cfcb0003f9b0003 0xc3cfcb0003f9b000

def z8 : W := mkw 0x0000000000000000 0x0000000000000000 0xe4004000c004093e 0x7e4004000c004093

def z9 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0x18ffb0003ffb0001 0x818ffb0003ffb000

def z10 : W := mkw 0x2800104340091110 0x8280010434009111 0x4000f007c01f0134 0x24000f007c01f013

def z11 : W := mkw 0x6800106340893910 0x8680010634089391 0x1004b4e7019b7001 0x01004b4e7019b700

def z12 : W := mkw 0x0000104240000000 0x8000010424000000 0xf404f4e7c0000000 0x3f404f4e7c000000

def z13 : W := mkw 0x69ffffffc089391f 0xc69ffffffc089391 0xfdffffffc19f793f 0x7fdffffffc19f793

def z14 : W := mkw 0x1009410882240269 0x0100941088224026 0x21184300c6040e32 0x121184300c6040e3

def z15 : W := mkw 0x81ffffdef776000f 0xf81ffffdef776000 0xfdffffffffff0007 0xffdffffffffff000

def z16 : W := mkw 0xa04be015127e118c 0x1a04be015127e118 0x4003f01f007f01c4 0x24003f01f007f01c

def z17 : W := mkw 0x804be0001276000c 0x1804be0001276000 0x4003f000007f0004 0x04003f000007f000

def z18 : W := mkw 0xc0ffeea03ff6ec0e 0x3c0ffeea03ff6ec0 0xffffffe03ffffe0f 0xdffffffe03ffffe0

def z19 : W := mkw 0x0009410880000009 0x0000941088000000 0xed1b4b18c0000000 0x3ed1b4b18c000000

def z20 : W := mkw 0x00200c0000000000 0x000200c000000000 0x9ce00c0000000000 0x09ce00c000000000

def z21 : W := mkw 0x0800104240010010 0x8080010424001001 0x00007000c0070030 0x000007000c007003

def z22 : W := mkw 0x0000000000000000 0x0000000000000000 0x02000000006081cc 0xc02000000006081c

def z23 : W := mkw 0x21f6bed75858d186 0xd21f6bed75858d18 0x10e4b4e738187001 0x010e4b4e73818700

def z24 : W := mkw 0x0009400002240008 0x0000940000224000 0x6c1b400006640006 0xc6c1b40000664000

def z25 : W := mkw 0x6800002100893910 0x0680000210089391 0x00000000019f793f 0x400000000019f793

def z26 : W := mkw 0x01201fdec0000003 0xc01201fdec000000 0x81000fffc0000000 0x381000fffc000000

def z27 : W := mkw 0x21629fdfd858d183 0xd21629fdfd858d18 0xdfe38ffff878f1cd 0xfdfe38ffff878f1c

def z28 : W := mkw 0x1009410882240269 0x0100941088224026 0x0b1b0b18066086c0 0x80b1b0b18066086c

def z29 : W := mkw 0x80ffee803f76c40e 0x380ffee803f76c40 0x7ffffb003fff8607 0xc7ffffb003fff860

def z30 : W := mkw 0x0009400002240008 0x0000940000224000 0xec1b4000c664093e 0xfec1b4000c664093

def z31 : W := mkw 0x409400202d80ec00 0x2409400202d80ec0 0x3efc00003f80fe0b 0xc3efc00003f80fe0

def z32 : W := mkw 0x11ffffdec224026f 0xc11ffffdec224026 0xfdffffffc6040e32 0x3fdffffffc6040e3

def z33 : W := mkw 0x014bf15ec000000d 0xc014bf15ec000000 0xed1bfb1fc0000000 0x3ed1bfb1fc000000

def z34 : W := mkw 0x11ffffdec224026f 0xc11ffffdec224026 0xffffffffc66086c0 0xbffffffffc66086c

def z35 : W := mkw 0x00b40e8000000002 0x000b40e800000000 0xbdfc0fe000000000 0x1bdfc0fe00000000

def z36 : W := mkw 0x01ffef9cad00c40f 0x601ffef9cad00c40 0x0bfb0b183e008600 0x80bfb0b183e00860

def z37 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z38 : W := mkw 0x90dfe108b776026d 0x390dfe108b776026 0xfffffb18ffff8fff 0xffffffb18ffff8ff

def z39 : W := mkw 0x00628c141850c080 0x100628c141850c08 0x0ae30818386080c0 0x80ae30818386080c

def z40 : W := mkw 0xa0ffec153f7ed18c 0x3a0ffec153f7ed18 0xfefffc1f3ffff1cf 0xefefffc1f3ffff1c

def z41 : W := mkw 0x0094000025000000 0x2009400002500000 0x3cfc00003f800003 0xc3cfc00003f80000

def z42 : W := mkw 0x11ffffdec224026f 0xc11ffffdec224026 0xffffffffc6648ffe 0xfffffffffc6648ff

def z43 : W := mkw 0x31ffffdfda7cd3ef 0xd31ffffdfda7cd3e 0xfffffffffe7cffff 0xffffffffffe7cfff

def z44 : W := mkw 0x400000202d80ec00 0x2400000202d80ec0 0x020000003f80fe0b 0xc020000003f80fe0

def z45 : W := mkw 0x01f6bed640000006 0xc01f6bed64000000 0x10e4b4e700000000 0x010e4b4e70000000

def z46 : W := mkw 0x41fffffeed80ec0f 0xe41fffffeed80ec0 0xffffffffff80fe0b 0xfffffffffff80fe0

def z47 : W := mkw 0x6800106340893910 0x8680010634089391 0xa00474e7c187793a 0x3a00474e7c187793

def z48 : W := mkw 0x91ffffdef776026f 0xf91ffffdef776026 0xffffffffffff8fff 0xfffffffffffff8ff

def z49 : W := mkw 0x7809516bc2ad3b79 0x87809516bc2ad3b7 0xff1fffffc7ffffff 0xfff1fffffc7fffff

def z50 : W := mkw 0x4000002000802800 0x0400000200080280 0xb40404e00180780b 0x5b40404e00180780

def z51 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0x50e7f00039ff0005 0x050e7f00039ff000

def z52 : W := mkw 0x2042801510581180 0x1204280151058118 0x4003801f007801c4 0x24003801f007801c

def z53 : W := mkw 0x409402a025802c02 0x2409402a025802c0 0x211c03e007800e02 0x1211c03e007800e0

def z54 : W := mkw 0x809d60002726000c 0x2809d60002726000 0x0018000006000000 0x0001800000600000

def z55 : W := mkw 0x306bcd1d9a7cd3e9 0x1306bcd1d9a7cd3e 0xfffbcf1ffe7cffff 0xffffbcf1ffe7cfff

def z56 : W := mkw 0x00b40e802d00c402 0x200b40e802d00c40 0x0bf80b003e008600 0x80bf80b003e00860

def z57 : W := mkw 0x40f68eb42d80ec02 0x240f68eb42d80ec0 0xffff8fff3f80fe0b 0xfffff8fff3f80fe0

def z58 : W := mkw 0x81ffef9cb776000f 0x781ffef9cb776000 0x7dfffb183fff0007 0xc7dfffb183fff000

def z59 : W := mkw 0x11295fdec224026b 0xc11295fdec224026 0xef1b4fffc6648ffe 0xfef1b4fffc6648ff

def z60 : W := mkw 0x0000000000000000 0x0000000000000000 0x9400040000007009 0x4940004000000700

def z61 : W := mkw 0x60b40ea13dd8fd82 0x360b40ea13dd8fd8 0xbffc0fe03ff8ffcf 0xdbffc0fe03ff8ffc

def z62 : W := mkw 0x20628c151858d180 0x120628c151858d18 0x8ae30c1f3860f1c8 0xa8ae30c1f3860f1c

def z63 : W := mkw 0x80d6a00037760004 0x380d6a0003776000 0x10e4b0003fff0007 0xc10e4b0003fff000

def z64 : W := mkw 0x0000104240000000 0x8000010424000000 0x200470e0c0000000 0x1200470e0c000000

def z65 : W := mkw 0x40200ea00880ec02 0x040200ea00880ec0 0x83000fe00000fe08 0x183000fe00000fe0

def z66 : W := mkw 0x80d6a00035520004 0x380d6a0003552000 0x10e4b000399b0001 0x010e4b000399b000

def z67 : W := mkw 0x6842906350d93910 0x96842906350d9391 0xfce7f4e7f9ff793f 0xffce7f4e7f9ff793

def z68 : W := mkw 0x50bd4fa8afa4ee6b 0x250bd4fa8afa4ee6 0xffff4ff8ffe4ffff 0xfffff4ff8ffe4fff

def z69 : W := mkw 0x68b41ee36d89fd12 0xa68b41ee36d89fd1 0xfffcffe7ff9fff3f 0xffffcffe7ff9fff3

def z70 : W := mkw 0x01ffffdeed00c40f 0xe01ffffdeed00c40 0xfffffffffe008600 0xbfffffffffe00860

def z71 : W := mkw 0x21f6bed75858d186 0xd21f6bed75858d18 0xdee7bcff3878f1cd 0xedee7bcff3878f1c

def z72 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0xbdfc0fe039807001 0x1bdfc0fe03980700

def z73 : W := mkw 0x014bf15ec000000d 0xc014bf15ec000000 0x4003f01fc0000000 0x24003f01fc000000

def z74 : W := mkw 0x01ffef9c8000000f 0x401ffef9c8000000 0x09fb0b1800000000 0x009fb0b180000000

def z75 : W := mkw 0xc1fffffefff6ec0f 0xfc1fffffefff6ec0 0xfffffffffffffe0f 0xffffffffffffffe0

def z76 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0x89fb0fffc0000000 0x389fb0fffc000000

def z77 : W := mkw 0x20628c151858d180 0x120628c151858d18 0x10e0840738187001 0x010e084073818700

def z78 : W := mkw 0xe9fffffff7ff391f 0xfe9fffffff7ff391 0xfdffffffffff793f 0xffdffffffffff793

def z79 : W := mkw 0x00628c1400000000 0x000628c140000000 0xdce38c1f00000000 0x2dce38c1f0000000

def z80 : W := mkw 0x0000000000000000 0x0000000000000000 0xce030818006081cc 0xece030818006081c

def z81 : W := mkw 0x0094000025000000 0x2009400002500000 0xbffc0b003f808e0b 0xdbffc0b003f808e0

def z82 : W := mkw 0x68201c774889f990 0x868201c774889f99 0x82000cffc000f9f8 0x382000cffc000f9f

def z83 : W := mkw 0x0042800010500000 0x1004280001050000 0x08e3000038600000 0x808e300003860000

def z84 : W := mkw 0xc8dff06277f7281c 0xbc8dff06277f7281 0x7cfff0e0ffff0837 0xd7cfff0e0ffff083

def z85 : W := mkw 0x4800106240812810 0x8480010624081281 0x000000e0c0000830 0x1000000e0c000083

def z86 : W := mkw 0x0042800010500000 0x1004280001050000 0x5ce3800038780005 0xc5ce380003878000

def z87 : W := mkw 0x01bd7fdec000000f 0xc01bd7fdec000000 0xa11c7fffc0000000 0x3a11c7fffc000000

def z88 : W := mkw 0x200000011858d180 0x1200000011858d18 0x020000003878f1cd 0xc020000003878f1c

def z89 : W := mkw 0x01f6ae9400000006 0x401f6ae940000000 0x00e0000000000000 0x000e000000000000

def z90 : W := mkw 0x20628c1510581180 0x120628c151058118 0xdce38c1f007801c4 0x2dce38c1f007801c

def z91 : W := mkw 0x6800002100893910 0x0680000210089391 0xe4004000c19f793f 0x7e4004000c19f793

def z92 : W := mkw 0x1000000002240260 0x0100000000224026 0x0200000006648ffe 0xc0200000006648ff

def z93 : W := mkw 0x6800106340893910 0x8680010634089391 0x800004e7c0007938 0x3800004e7c000793

def z94 : W := mkw 0x8000000037760000 0x3800000003776000 0x000000003fff0007 0xc000000003fff000

def z95 : W := mkw 0x00628c1400000000 0x000628c140000000 0xdee38c1f006081cc 0xedee38c1f006081c

def z96 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0x08fb00003e600000 0x808fb00003e60000

def z97 : W := mkw 0xd0ffefa8bff6ee6f 0x3d0ffefa8bff6ee6 0xfffffff8ffffffff 0xffffffff8fffffff

def z98 : W := mkw 0x00dff0424000000c 0x800dff0424000000 0xfcfff4e7c0000000 0x3fcfff4e7c000000

def z99 : W := mkw 0x20200c150808d180 0x020200c150808d18 0x82000c1f0000f1c8 0x282000c1f0000f1c

def z100 : W := mkw 0x814bf15ed276000d 0xd814bf15ed276000 0x4003f01fc07f0004 0x24003f01fc07f000

def z101 : W := mkw 0x70ffcfbdbffcffeb 0x370ffcfbdbffcffe 0xffffcffffffcffff 0xfffffcffffffcfff

def z102 : W := mkw 0x10294d088a24c269 0x010294d088a24c26 0xfffb4f18fe64ffff 0xffffb4f18fe64fff

def z103 : W := mkw 0x41fffffec880ec0f 0xc41fffffec880ec0 0xffffffffc000fe08 0x3ffffffffc000fe0

def z104 : W := mkw 0x90dfe108b776026d 0x390dfe108b776026 0xeffb4b18fe648ffe 0xfeffb4b18fe648ff

def z105 : W := mkw 0x0000000000000000 0x0000000000000000 0x7404f00000000000 0x07404f0000000000

def z106 : W := mkw 0x0094000025000000 0x2009400002500000 0x7cfcf0003f9f0007 0xc7cfcf0003f9f000

def z107 : W := mkw 0x40bd4fa8ad80ec0b 0x240bd4fa8ad80ec0 0xffff4ff8ff80fe0b 0xfffff4ff8ff80fe0

def z108 : W := mkw 0x80dfe0003552000c 0x380dfe0003552000 0x7cfff000399b0001 0x07cfff000399b000

def z109 : W := mkw 0x80d6a00035520004 0x380d6a0003552000 0x5ce7b00039fb0005 0xc5ce7b00039fb000

def z110 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0x50e7f4ffc0000000 0x250e7f4ffc000000

def z111 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0x10e404e039807001 0x010e404e03980700

def z112 : W := mkw 0x1009410882240269 0x0100941088224026 0x40034018c06401f4 0x240034018c06401f

def z113 : W := mkw 0x0094028025000402 0x2009402802500040 0x0118030006000600 0x0011803000600060

def z114 : W := mkw 0x4800106240812810 0x8480010624081281 0x200470e0c1870832 0x1200470e0c187083

def z115 : W := mkw 0x4800106240812810 0x8480010624081281 0x7404f0e0c19f0837 0x57404f0e0c19f083

def z116 : W := mkw 0x809d60002726000c 0x2809d60002726000 0x201c700007870002 0x0201c70000787000

def z117 : W := mkw 0x21ffffdfd058118f 0xd21ffffdfd058118 0xfdffffffc07801c4 0x3fdffffffc07801c

def z118 : W := mkw 0x21ffffdfd858d18f 0xd21ffffdfd858d18 0xfffffffff878f1cd 0xffffffffff878f1c

def z119 : W := mkw 0x68629c7758d9f990 0x968629c7758d9f99 0xfee7fcfff9fff9ff 0xffee7fcfff9fff9f

def z120 : W := mkw 0x6800106340893910 0x8680010634089391 0x5004f4e7c19f7135 0x25004f4e7c19f713

def z121 : W := mkw 0x804be0001276000c 0x1804be0001276000 0x7407f00001ff0007 0x47407f00001ff000

def z122 : W := mkw 0xe8dff06377ff391c 0xbe8dff06377ff391 0xfcfff4e7ffff793f 0xffcfff4e7ffff793

def z123 : W := mkw 0x01200f9c80000003 0x401200f9c8000000 0x01000b1800000000 0x001000b180000000

def z124 : W := mkw 0x80dfe0001276000c 0x180dfe0001276000 0x7cfff000007f0004 0x07cfff000007f000

def z125 : W := mkw 0x20628c151858d180 0x120628c151858d18 0x50e3841f387871c5 0x250e3841f387871c

def z126 : W := mkw 0x01201fdec0000003 0xc01201fdec000000 0xf504ffffc0000000 0x3f504ffffc000000

def z127 : W := mkw 0x019d73cac000000f 0xc019d73cac000000 0x211c73e0c0000000 0x1211c73e0c000000

def z128 : W := mkw 0x00628c1410500000 0x100628c141050000 0xdce38c1f38780005 0xedce38c1f3878000

def z129 : W := mkw 0x00200c000800c000 0x000200c000800c00 0x9ee00c003800f009 0xc9ee00c003800f00

def z130 : W := mkw 0x01dff3dec000000f 0xc01dff3dec000000 0x611ff3ffc0000000 0x3611ff3ffc000000

def z131 : W := mkw 0x01ffffdee500000f 0xe01ffffdee500000 0xfdffffffff800003 0xffdffffffff80000

def z132 : W := mkw 0x6800106340893910 0x8680010634089391 0xfe07fcffc1fff9ff 0xffe07fcffc1fff9f

def z133 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0x19ffbfff00000000 0x019ffbfff0000000

def z134 : W := mkw 0x0009400002240008 0x0000940000224000 0x7c1ff00007ff0007 0xc7c1ff00007ff000

def z135 : W := mkw 0x80ffee803f76c40e 0x380ffee803f76c40 0x0bfb0b003e608600 0x80bfb0b003e60860

def z136 : W := mkw 0x000000000800c000 0x0000000000800c00 0x020000003800f009 0xc020000003800f00

def z137 : W := mkw 0x419d73eae5802c0f 0xe419d73eae5802c0 0x211c73e0c7800e02 0x1211c73e0c7800e0

def z138 : W := mkw 0x00b40e8025000002 0x200b40e802500000 0xbdfc0fe03f800003 0xdbdfc0fe03f80000

def z139 : W := mkw 0x1009514ac2240269 0x81009514ac224026 0xff1fffffc6648ffe 0xfff1fffffc6648ff

def z140 : W := mkw 0x306bcd1d9a7cd3e9 0x1306bcd1d9a7cd3e 0xdee3cc1ff87cf1fd 0xedee3cc1ff87cf1f

def z141 : W := mkw 0x0000000000000000 0x0000000000000000 0xaf180b0006008e0a 0xdaf180b0006008e0

def z142 : W := mkw 0xe800106377ff3910 0xbe800106377ff391 0xf404f4e7ffff793f 0xff404f4e7ffff793

def z143 : W := mkw 0x6809506342ad3918 0x86809506342ad391 0xfc1ff4e7c7ff793f 0xffc1ff4e7c7ff793

def z144 : W := mkw 0x2000000100081100 0x0200000010008110 0xf404f407019f710f 0x6f404f407019f710

def z145 : W := mkw 0x6800106340893910 0x8680010634089391 0xff1cffe7c79fff3f 0xfff1cffe7c79fff3

def z146 : W := mkw 0x20628c151858d180 0x120628c151858d18 0xfee7fc1f39fff1cf 0xefee7fc1f39fff1c

def z147 : W := mkw 0x0000000000000000 0x0000000000000000 0x7404f000019f0007 0x47404f000019f000

def z148 : W := mkw 0x8000000035520000 0x3800000003552000 0x00000000399b0001 0x000000000399b000

def z149 : W := mkw 0x80ffec143776000c 0x380ffec143776000 0xfcfffc1f3fff0007 0xefcfffc1f3fff000

def z150 : W := mkw 0x200000011858d180 0x1200000011858d18 0xd60084073878f1cd 0xed60084073878f1c

def z151 : W := mkw 0x81ffef9cb776000f 0x781ffef9cb776000 0x09fb0b183e600000 0x809fb0b183e60000

def z152 : W := mkw 0x1000000002240260 0x0100000000224026 0x02000000066086c0 0x802000000066086c

def z153 : W := mkw 0x6800002100893910 0x0680000210089391 0x0000000000007938 0x0000000000000793

def z154 : W := mkw 0x00dfe0000224000c 0x000dfe0000224000 0x7cfff00006640006 0xc7cfff0000664000

def z155 : W := mkw 0x0009410880000009 0x0000941088000000 0xef1b4b18c06081cc 0xfef1b4b18c06081c

def z156 : W := mkw 0x80d6a00035520004 0x380d6a0003552000 0x00e0000038000000 0x000e000003800000

def z157 : W := mkw 0x680000212d89fd10 0x2680000212d89fd1 0x020000003f9fff3f 0xc020000003f9fff3

def z158 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0xfefff8183fff81cf 0xefefff8183fff81c

def z159 : W := mkw 0x1000010880000261 0x0100001088000026 0x83000b18c0008ff8 0x383000b18c0008ff

def z160 : W := mkw 0x1009410882240269 0x0100941088224026 0x6d1b4300c6640e36 0xd6d1b4300c6640e3

def z161 : W := mkw 0x6800106340893910 0x8680010634089391 0xc000f4e7c01f793c 0x3c000f4e7c01f793

def z162 : W := mkw 0x200000010808d180 0x0200000010808d18 0x020000000000f1c8 0x0020000000000f1c

def z163 : W := mkw 0x0042800010500000 0x1004280001050000 0x10e0800038180001 0x010e080003818000

def z164 : W := mkw 0x1009410882240269 0x0100941088224026 0x8b1b0b18c6608ff8 0xb8b1b0b18c6608ff

def z165 : W := mkw 0x1000000002240260 0x0100000000224026 0x0000000006040e32 0x00000000006040e3

def z166 : W := mkw 0x4000106240802800 0x8400010624080280 0xf404f4e7c180780b 0x7f404f4e7c180780

def z167 : W := mkw 0x90dfe108b776026d 0x390dfe108b776026 0x7dfff300ffff0e37 0xd7dfff300ffff0e3

def z168 : W := mkw 0x909d6108a726026d 0x2909d6108a726026 0xef1f7b18c7e78ffe 0xfef1f7b18c7e78ff

def z169 : W := mkw 0x1000010882240261 0x0100001088224026 0x83000b18c6648ffe 0xf83000b18c6648ff

def z170 : W := mkw 0x6800002100893910 0x0680000210089391 0x7404f000019f793f 0x47404f000019f793

def z171 : W := mkw 0x01ffffdec800c00f 0xc01ffffdec800c00 0xfffffffff800f009 0xffffffffff800f00

def z172 : W := mkw 0x2000000100081100 0x0200000010008110 0x000000000018710d 0x4000000000018710

def z173 : W := mkw 0x4800106240812810 0x8480010624081281 0xe40470e0c187093e 0x7e40470e0c187093

def z174 : W := mkw 0x0000010880000001 0x0000001088000000 0x81000b18c0000000 0x381000b18c000000

def z175 : W := mkw 0x79ffffffc2ad3b7f 0xc79ffffffc2ad3b7 0xffffffffc7ffffff 0xfffffffffc7fffff

def z176 : W := mkw 0x69201fffc0893913 0xc69201fffc089391 0xf504ffffc19f793f 0x7f504ffffc19f793

def z177 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xffffffffc06081cc 0xfffffffffc06081c

def z178 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0xffff0ff83fe0ffcf 0xfffff0ff83fe0ffc

def z179 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0xfffffb003fff8e0f 0xdfffffb003fff8e0

def z180 : W := mkw 0x41b41ffeed80ec03 0xe41b41ffeed80ec0 0xbffc0fffff80fe0b 0xfbffc0fffff80fe0

def z181 : W := mkw 0x6842907750d93990 0x96842907750d9399 0xf407f4ffc1ff79ff 0x7f407f4ffc1ff79f

def z182 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0xfcfff000ffff093f 0xffcfff000ffff093

def z183 : W := mkw 0x019d63888000000f 0x4019d63888000000 0x0118030000000000 0x0011803000000000

def z184 : W := mkw 0x01ffef9c8000000f 0x401ffef9c8000000 0xedfb4b18c0000000 0x3edfb4b18c000000

def z185 : W := mkw 0x0094000025000000 0x2009400002500000 0x08f800003e000000 0x808f800003e00000

def z186 : W := mkw 0x00b40e802d00c402 0x200b40e802d00c40 0x3ffc0b003f808603 0xc3ffc0b003f80860

def z187 : W := mkw 0x6800002100893910 0x0680000210089391 0x00000000019b7001 0x000000000019b700

def z188 : W := mkw 0x6800106340893910 0x8680010634089391 0xf404f4e7c0007938 0x3f404f4e7c000793

def z189 : W := mkw 0x306bcd1d9a7cd3e9 0x1306bcd1d9a7cd3e 0xdffb8f1f3e78f7cd 0xedffb8f1f3e78f7c

def z190 : W := mkw 0x68629c7758d9f990 0x968629c7758d9f99 0x10e4b4e7399b7001 0x010e4b4e7399b700

def z191 : W := mkw 0x01ffffded850c08f 0xd01ffffded850c08 0xfffffffff86080c0 0xbfffffffff86080c

def z192 : W := mkw 0x2042801510581180 0x1204280151058118 0x5ce3801f387801c5 0xe5ce3801f387801c

def z193 : W := mkw 0xc0ffeea03ff6ec0e 0x3c0ffeea03ff6ec0 0xbfff0fe03fe0fe0b 0xdbfff0fe03fe0fe0

def z194 : W := mkw 0x41f6bef66d80ec06 0xe41f6bef66d80ec0 0x10e4b4e739807001 0x010e4b4e73980700

def z195 : W := mkw 0x20200c150808d180 0x020200c150808d18 0xce030c1f0060f1cc 0xece030c1f0060f1c

def z196 : W := mkw 0xa06bec151a7ed18c 0x1a06bec151a7ed18 0xdee3fc1f387ff1cd 0xedee3fc1f387ff1c

def z197 : W := mkw 0xa1ffffdfff7ed18f 0xfa1ffffdfff7ed18 0xfffffffffffff1cf 0xffffffffffffff1c

def z198 : W := mkw 0x68629c7740893910 0x868629c774089391 0xfce7fcffc19f793f 0x7fce7fcffc19f793

def z199 : W := mkw 0x00dfe0000000000c 0x000dfe0000000000 0x7cfff00000000000 0x07cfff0000000000

def z200 : W := mkw 0x20200c010808d100 0x020200c010808d10 0xdee08c073818f10d 0xedee08c073818f10

def z201 : W := mkw 0x4000002000802800 0x0400000200080280 0xf404f4e0019f780f 0x5f404f4e0019f780

def z202 : W := mkw 0x0000104240000000 0x8000010424000000 0x1004b4e700000000 0x01004b4e70000000

def z203 : W := mkw 0x20200c150808d180 0x020200c150808d18 0x9ee00c1f3800f1c9 0xe9ee00c1f3800f1c

def z204 : W := mkw 0x0094000000000000 0x0009400000000000 0x3cfc000000000000 0x03cfc00000000000

def z205 : W := mkw 0x60f68eb53dd8fd82 0x360f68eb53dd8fd8 0x10e484e739987001 0x010e484e73998700

def z206 : W := mkw 0x1000000002240260 0x0100000000224026 0xaf180b0006648ffe 0xdaf180b0006648ff

def z207 : W := mkw 0xf8dff16bf7ff3b7d 0xbf8dff16bf7ff3b7 0xffffffffffffffff 0xffffffffffffffff

def z208 : W := mkw 0x00628c141850c080 0x100628c141850c08 0xdee38c1f386080c0 0xadee38c1f386080c

def z209 : W := mkw 0x2000000100081100 0x0200000010008110 0xd40084070018710d 0x6d40084070018710

def z210 : W := mkw 0x01629fdec0000003 0xc01629fdec000000 0xdde38fffc0000000 0x3dde38fffc000000

def z211 : W := mkw 0x80dfe108b776000d 0x380dfe108b776000 0xfdfffb18ffff0007 0xffdfffb18ffff000

def z212 : W := mkw 0x80dfe0002726000c 0x280dfe0002726000 0x7cfff00007870002 0x07cfff0000787000

def z213 : W := mkw 0x00200e8000000002 0x000200e800000000 0x81000fe000000000 0x181000fe00000000

def z214 : W := mkw 0x80d6a00035520004 0x380d6a0003552000 0x74e4f000399f0007 0x474e4f000399f000

def z215 : W := mkw 0x7809516bc2ad3b79 0x87809516bc2ad3b7 0xef1b4fffc664fffe 0xfef1b4fffc664fff

def z216 : W := mkw 0x68b41ee36d89fd12 0xa68b41ee36d89fd1 0xbffc0fe7ff80ff3b 0xfbffc0fe7ff80ff3

def z217 : W := mkw 0x81ffffdef552000f 0xf81ffffdef552000 0xfdfffffff99b0001 0x3fdfffffff99b000

def z218 : W := mkw 0x20628c151858d180 0x120628c151858d18 0x0ae308183878f1cd 0xc0ae308183878f1c

def z219 : W := mkw 0x0094000025000000 0x2009400002500000 0x10e4000039800001 0x010e400003980000

def z220 : W := mkw 0x40200ea00880ec02 0x040200ea00880ec0 0x000004e000007000 0x0000004e00000700

def z221 : W := mkw 0x60f68eb53dd8fd82 0x360f68eb53dd8fd8 0xffff8fff3ff8ffcf 0xfffff8fff3ff8ffc

def z222 : W := mkw 0xc0f6aea03dd2ec06 0x3c0f6aea03dd2ec0 0x10e4b4e0399b7001 0x010e4b4e0399b700

def z223 : W := mkw 0x6800106340893910 0x8680010634089391 0xf404f4e7c19b7001 0x3f404f4e7c19b700

def z224 : W := mkw 0x400000202d80ec00 0x2400000202d80ec0 0x0000000039807001 0x0000000003980700

def z225 : W := mkw 0x300941099a7cd3e9 0x1300941099a7cd3e 0xef1b4b18fe7cffff 0xfef1b4b18fe7cfff

def z226 : W := mkw 0x01f6bed640000006 0xc01f6bed64000000 0xf4e4f4e7c0000000 0x3f4e4f4e7c000000

def z227 : W := mkw 0x1009410882240269 0x0100941088224026 0xcf1b0b18066087cc 0xecf1b0b18066087c

def z228 : W := mkw 0x0000000000000000 0x0000000000000000 0x2004700001870002 0x0200470000187000

def z229 : W := mkw 0x01ffffded050000f 0xd01ffffded050000 0xfdfffffff8780005 0xffdfffffff878000

def z230 : W := mkw 0x8042800037760000 0x3804280003776000 0x5ce380003fff0007 0xc5ce380003fff000

def z231 : W := mkw 0x1000010880000261 0x0100001088000026 0xe7004b18c0048ffe 0x7e7004b18c0048ff

def z232 : W := mkw 0x019d73cac000000f 0xc019d73cac000000 0xf51cf7e7c0000000 0x3f51cf7e7c000000

def z233 : W := mkw 0x016bffdec000000f 0xc016bffdec000000 0xc103ffffc0000000 0x3c103ffffc000000

def z234 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0x31fcf7e7c0000000 0x131fcf7e7c000000

def z235 : W := mkw 0x7800002102ad3b70 0x07800002102ad3b7 0x0200000007ffffff 0xc0200000007fffff

def z236 : W := mkw 0x106bcd1c9a74c2e9 0x1106bcd1c9a74c2e 0xeffb4b18fe648ffe 0xfeffb4b18fe648ff

def z237 : W := mkw 0x1009410882240269 0x0100941088224026 0x6f1b4b18066486c6 0xc6f1b4b18066486c

def z238 : W := mkw 0x20628c151858d180 0x120628c151858d18 0xdce38c1f38187001 0x2dce38c1f3818700

def z239 : W := mkw 0x1000000002240260 0x0100000000224026 0x00000000006401f4 0x000000000006401f

def z240 : W := mkw 0x0000000000000000 0x0000000000000000 0xf404f000c19f093f 0x7f404f000c19f093

def z241 : W := mkw 0x2842905750591190 0x9284290575059119 0x4003f01fc07f01f4 0x24003f01fc07f01f

def z242 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0x7cfff0003e600000 0x87cfff0003e60000

def z243 : W := mkw 0x0000000000000000 0x0000000000000000 0x0b180b0006008600 0x80b180b000600860

def z244 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0x49fbfb1fc0000000 0x249fbfb1fc000000

def z245 : W := mkw 0x300000011a7cd3e0 0x1300000011a7cd3e 0x020000003e7cffff 0xc020000003e7cfff

def z246 : W := mkw 0xa0f6ac153d5ad184 0x3a0f6ac153d5ad18 0xdee7bc1f39fbf1cd 0xedee7bc1f39fbf1c

def z247 : W := mkw 0x6800002100893910 0x0680000210089391 0xd4008407019f793f 0x6d4008407019f793

def z248 : W := mkw 0x6800106340893910 0x8680010634089391 0x800004e7c19f793f 0x7800004e7c19f793

def z249 : W := mkw 0x50b40fa8ad80ee63 0x250b40fa8ad80ee6 0xbffc0ff8ff80fffb 0xfbffc0ff8ff80fff

def z250 : W := mkw 0x01f6bfdec0000007 0xc01f6bfdec000000 0x91e4bfffc0000000 0x391e4bfffc000000

def z251 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0x93e40fe03980fe09 0x193e40fe03980fe0

def z252 : W := mkw 0x00b40e800800c002 0x000b40e800800c00 0xbffc0fe03800f009 0xdbffc0fe03800f00

def z253 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0x0bf80b003f80fe0b 0xc0bf80b003f80fe0

def z254 : W := mkw 0x2800104340091110 0x8280010434009111 0xd400f407c01f713d 0x6d400f407c01f713

def z255 : W := mkw 0x10bd4f88af24c66b 0x210bd4f88af24c66 0x0bfb0b183e6086c0 0x80bfb0b183e6086c

def z256 : W := mkw 0x01201ed640000002 0xc01201ed64000000 0x000004e700000000 0x0000004e70000000

def z257 : W := mkw 0x6800106358d9f990 0x96800106358d9f99 0xf604f4e7f9fff9ff 0xff604f4e7f9fff9f

def z258 : W := mkw 0x2042801510581180 0x1204280151058118 0x0000800700180000 0x0000080070018000

def z259 : W := mkw 0x0000000000000000 0x0000000000000000 0x80000000c0000938 0x380000000c000093

def z260 : W := mkw 0x00ffec140000000c 0x000ffec140000000 0xfcfffc1f00000000 0x2fcfffc1f0000000

def z261 : W := mkw 0x1009410882240269 0x0100941088224026 0xff1ffb18c7ff8fff 0xfff1ffb18c7ff8ff

def z262 : W := mkw 0x6800106340893910 0x8680010634089391 0x6004f0e7c19f0936 0x36004f0e7c19f093

def z263 : W := mkw 0x40200ea00880ec02 0x040200ea00880ec0 0xb7040fe00180fe0b 0x5b7040fe00180fe0

def z264 : W := mkw 0x50bd4fa8afa4ee6b 0x250bd4fa8afa4ee6 0xbfff0ff83fe0fecb 0xdbfff0ff83fe0fec

def z265 : W := mkw 0x20628c151858d180 0x120628c151858d18 0x5ce3840738787005 0xc5ce384073878700

def z266 : W := mkw 0x68201c634889f910 0x868201c634889f91 0xfee4fce7f99ff93f 0xffee4fce7f99ff93

def z267 : W := mkw 0x5809516ac2a52a79 0x85809516ac2a52a7 0xef1f7bf8c7e78ffe 0xfef1f7bf8c7e78ff

def z268 : W := mkw 0x01f6bed640000006 0xc01f6bed64000000 0xdce7bcff00000000 0x2dce7bcff0000000

def z269 : W := mkw 0x0042800010500000 0x1004280001050000 0xdee38818387881cd 0xedee38818387881c

def z270 : W := mkw 0x809d60002726000c 0x2809d60002726000 0x3cfc70003f870003 0xc3cfc70003f87000

def z271 : W := mkw 0xa0ffec153f7ed18c 0x3a0ffec153f7ed18 0x7cfff4073fff7007 0xc7cfff4073fff700

def z272 : W := mkw 0x40b41ee26d80ec02 0xa40b41ee26d80ec0 0xfffcffe7ff80fe0b 0xffffcffe7ff80fe0

def z273 : W := mkw 0x6800106340893910 0x8680010634089391 0xb40404e7c180793b 0x7b40404e7c180793

def z274 : W := mkw 0x409402a025802c02 0x2409402a025802c0 0xaf1c0be007808e0a 0xdaf1c0be007808e0

def z275 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0x8bf80fe03e00fe08 0x98bf80fe03e00fe0

def z276 : W := mkw 0x1009410880000269 0x0100941088000026 0xef1b4b18c0008ff8 0x3ef1b4b18c0008ff

def z277 : W := mkw 0x50200fa88880ee63 0x050200fa88880ee6 0x83000ff8c000fff8 0x383000ff8c000fff

def z278 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xfdffffffc19f0007 0x7fdffffffc19f000

def z279 : W := mkw 0xe800002137ff3910 0x3e800002137ff391 0x000000003fff793f 0xc000000003fff793

def z280 : W := mkw 0x61fffffffdd8fd8f 0xf61fffffffdd8fd8 0xfffffffffff8ffcf 0xffffffffffff8ffc

def z281 : W := mkw 0x40b40ea00880ec02 0x040b40ea00880ec0 0xbffc0fe00000fe08 0x1bffc0fe00000fe0

def z282 : W := mkw 0x51fffffeefa4ee6f 0xe51fffffeefa4ee6 0xffffffffffe4ffff 0xfffffffffffe4fff

def z283 : W := mkw 0xa8dff043777f111c 0xba8dff043777f111 0x7cfff007ffff0137 0xe7cfff007ffff013

def z284 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000f000001f0004 0x04000f000001f000

def z285 : W := mkw 0x1009410882240269 0x0100941088224026 0x00004000c0040030 0x000004000c004003

def z286 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0xfffcffe03f9ffe0f 0xdfffcffe03f9ffe0

def z287 : W := mkw 0x0000000000000000 0x0000000000000000 0xb40404e000000000 0x1b40404e00000000

def z288 : W := mkw 0x0000104240000000 0x8000010424000000 0x800004e7c0000000 0x3800004e7c000000

def z289 : W := mkw 0x6800002118d9f990 0x16800002118d9f99 0x0200000039fff9ff 0xc0200000039fff9f

def z290 : W := mkw 0x6894106365893910 0xa689410636589391 0xfcfcf4e7ff9f793f 0xffcfcf4e7ff9f793

def z291 : W := mkw 0x00b40e8000000002 0x000b40e800000000 0x10e404e000000000 0x010e404e00000000

def z292 : W := mkw 0x00628c141850c080 0x100628c141850c08 0xcee30818386081cc 0xecee30818386081c

def z293 : W := mkw 0x0042800010500000 0x1004280001050000 0x4003800000780004 0x0400380000078000

def z294 : W := mkw 0x3809514bc22d1379 0x83809514bc22d137 0xef1bfb1fc67f8ffe 0xfef1bfb1fc67f8ff

def z295 : W := mkw 0x400000202d80ec00 0x2400000202d80ec0 0xb60404e03f80fe0b 0xdb60404e03f80fe0

def z296 : W := mkw 0x00628c141850c080 0x100628c141850c08 0x00e0000038000000 0x000e000003800000

def z297 : W := mkw 0x60628c353dd8fd80 0x360628c353dd8fd8 0xdee38c1f3ff8ffcf 0xedee38c1f3ff8ffc

def z298 : W := mkw 0x0009410880000009 0x0000941088000000 0xef1b4b18c6008e0a 0xfef1b4b18c6008e0

def z299 : W := mkw 0x00200c1400000000 0x000200c140000000 0x80000c1f00000000 0x280000c1f0000000

def z300 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0x28ff70003fe70002 0x828ff70003fe7000

def z301 : W := mkw 0x10dfe1088224026d 0x010dfe1088224026 0xfffffb18c6648ffe 0xffffffb18c6648ff

def z302 : W := mkw 0x00629c5640000000 0x800629c564000000 0xfce7fcffc0000000 0x3fce7fcffc000000

def z303 : W := mkw 0x0094000025000000 0x2009400002500000 0x201c000007800002 0x0201c00000780000

def z304 : W := mkw 0x49fffffec081281f 0xc49fffffec081281 0xfdffffffc1870832 0x3fdffffffc187083

def z305 : W := mkw 0x69f6bef740893916 0xc69f6bef74089391 0x10e4b4e7019b7001 0x010e4b4e7019b700

def z306 : W := mkw 0x20629c575858d180 0x920629c575858d18 0xfee7fcfff878f1cd 0xffee7fcfff878f1c

def z307 : W := mkw 0x41fffffeed80ec0f 0xe41fffffeed80ec0 0xfdfffffff9807001 0x3fdfffffff980700

def z308 : W := mkw 0x119d73cac224026f 0xc119d73cac224026 0x211c73e0c6040e32 0x1211c73e0c6040e3

def z309 : W := mkw 0x80dff0427776000c 0xb80dff0427776000 0xfcfff4e7ffff0007 0xffcfff4e7ffff000

def z310 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0x1bfc0fe03f80f601 0x81bfc0fe03f80f60

def z311 : W := mkw 0xb0ffed1dbf7ed3ed 0x3b0ffed1dbf7ed3e 0xffffff1fffffffff 0xfffffff1ffffffff

def z312 : W := mkw 0x00b40e802d00c402 0x200b40e802d00c40 0x9ff80f003e00f609 0xc9ff80f003e00f60

def z313 : W := mkw 0x00d6a00000000004 0x000d6a0000000000 0x10e4b00000000000 0x010e4b0000000000

def z314 : W := mkw 0x0000000000000000 0x0000000000000000 0xd400840700000000 0x2d40084070000000

def z315 : W := mkw 0x01295fdec000000b 0xc01295fdec000000 0xed1b4fffc0000000 0x3ed1b4fffc000000

def z316 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0x29ff7bf8c0000000 0x129ff7bf8c000000

def z317 : W := mkw 0x81fffed67776000e 0xf81fffed67776000 0x7cfff4e73fff0007 0xc7cfff4e73fff000

def z318 : W := mkw 0x6800106340893910 0x8680010634089391 0x3004f4e7c19f7833 0x13004f4e7c19f783

def z319 : W := mkw 0x809d60002726000c 0x2809d60002726000 0x741cf000079f0007 0x4741cf000079f000

def z320 : W := mkw 0x6800106340893910 0x8680010634089391 0x000004e700007000 0x0000004e70000700

def z321 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000019f0007 0x400000000019f000

def z322 : W := mkw 0x1009410882240269 0x0100941088224026 0x2b1b4b18c6648ef2 0x92b1b4b18c6648ef

def z323 : W := mkw 0x69ffffffc089391f 0xc69ffffffc089391 0xfdffffffc19b7001 0x3fdffffffc19b700

def z324 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000004093e 0x4000000000004093

def z325 : W := mkw 0x00b41ec240000002 0x800b41ec24000000 0xfdfcffe7c0000000 0x3fdfcffe7c000000

def z326 : W := mkw 0x2800000100091110 0x0280000010009111 0x00000000001f0134 0x000000000001f013

def z327 : W := mkw 0x20628c151858d180 0x120628c151858d18 0xfffb8f1f3e78ffcf 0xffffb8f1f3e78ffc

def z328 : W := mkw 0x6800106340893910 0x8680010634089391 0xd40084e7c018793d 0x7d40084e7c018793

def z329 : W := mkw 0x0000000000000000 0x0000000000000000 0x0200000006008e0a 0xc0200000006008e0

def z330 : W := mkw 0x00b40e802d00c402 0x200b40e802d00c40 0xbffc0fe03e008600 0x9bffc0fe03e00860

def z331 : W := mkw 0x80ffec143f76c08c 0x380ffec143f76c08 0x7efff8183fff80c7 0xc7efff8183fff80c

def z332 : W := mkw 0x2000000110581180 0x1200000011058118 0x00000000007801c4 0x000000000007801c

def z333 : W := mkw 0x68201c774889f990 0x868201c774889f99 0xf604fcffc19ff9ff 0x7f604fcffc19ff9f

def z334 : W := mkw 0x1000010880000261 0x0100001088000026 0x01000300c0000e30 0x101000300c0000e3

def z335 : W := mkw 0x01ffef9c8000000f 0x401ffef9c8000000 0x7dfffb1800000000 0x07dfffb180000000

def z336 : W := mkw 0x00628c1400000000 0x000628c140000000 0x08e3081800000000 0x008e308180000000

def z337 : W := mkw 0x9000000037760260 0x3900000003776026 0x020000003fff8fff 0xc020000003fff8ff

def z338 : W := mkw 0x8042a00010520004 0x18042a0001052000 0x0000b000001b0000 0x00000b000001b000

def z339 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0xfffc4fe0ff84ff3f 0xffffc4fe0ff84ff3

def z340 : W := mkw 0x509d43a8a7a42e6b 0x2509d43a8a7a42e6 0xef1f4bf8c7e48ffe 0xfef1f4bf8c7e48ff

def z341 : W := mkw 0x1009410882240269 0x0100941088224026 0x23184300c6648ffe 0xd23184300c6648ff

def z342 : W := mkw 0x216bfd5fd858d18d 0xd216bfd5fd858d18 0xdee3fc1ff878f1cd 0xedee3fc1ff878f1c

def z343 : W := mkw 0xc0f6aea03dd2ec06 0x3c0f6aea03dd2ec0 0xbffcbfe03f9bfe0b 0xdbffcbfe03f9bfe0

def z344 : W := mkw 0x00628c1400000000 0x000628c140000000 0x10e0840700000000 0x010e084070000000

def z345 : W := mkw 0x81ffffdee726000f 0xe81ffffdee726000 0xfdffffffc7870002 0x3fdffffffc787000

def z346 : W := mkw 0x1009410882240269 0x0100941088224026 0x0b1b0b1806648ffe 0xc0b1b0b1806648ff

def z347 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0x08fb00003fff0007 0xc08fb00003fff000

def z348 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xfdffffffc004093e 0x7fdffffffc004093

def z349 : W := mkw 0x200000011858d180 0x1200000011858d18 0x0000000038187001 0x0000000003818700

def z350 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0x601ff00007ff0006 0x0601ff00007ff000

def z351 : W := mkw 0x0000000000000000 0x0000000000000000 0x8e00080000008008 0xc8e0008000000800

def z352 : W := mkw 0x1009410882240269 0x0100941088224026 0xaf184b00c6048e3a 0xdaf184b00c6048e3

def z353 : W := mkw 0x40f68eb43dd0ec82 0x340f68eb43dd0ec8 0xbfff0ff83fe0fecb 0xdbfff0ff83fe0fec

def z354 : W := mkw 0x11ffef9c8224026f 0x411ffef9c8224026 0xeffb4b18c6648ffe 0xfeffb4b18c6648ff

def z355 : W := mkw 0x4000002000802800 0x0400000200080280 0x200400e001800802 0x1200400e00180080

def z356 : W := mkw 0x8000000037760000 0x3800000003776000 0x000000003e600000 0x8000000003e60000

def z357 : W := mkw 0x90dfe108b776026d 0x390dfe108b776026 0x0bfb0b183e6086c0 0x80bfb0b183e6086c

def z358 : W := mkw 0x80ffec003f76c00c 0x380ffec003f76c00 0xfefffc003ffff00f 0xcfefffc003ffff00

def z359 : W := mkw 0x6809516bc0893919 0x86809516bc089391 0xfd1fffffc19f793f 0x7fd1fffffc19f793

def z360 : W := mkw 0x8000000012760000 0x1800000001276000 0x00000000007f0004 0x000000000007f000

def z361 : W := mkw 0x1009410882240269 0x0100941088224026 0x6c1b4018c66401f6 0xe6c1b4018c66401f

def z362 : W := mkw 0x000000001850c080 0x1000000001850c08 0x02000000386080c0 0x802000000386080c

def z363 : W := mkw 0x0000000000000000 0x0000000000000000 0x2118030006000e02 0x12118030006000e0

def z364 : W := mkw 0x00200c000800c000 0x000200c000800c00 0x82000c000000f008 0x082000c000000f00

def z365 : W := mkw 0x20200c150808d180 0x020200c150808d18 0x0000040700007000 0x0000004070000700

def z366 : W := mkw 0x11ffffdec000026f 0xc11ffffdec000026 0xffffffffc0008ff8 0x3ffffffffc0008ff

def z367 : W := mkw 0x010013cac0000003 0xc010013cac000000 0x010003e0c0000000 0x1010003e0c000000

def z368 : W := mkw 0x00dfe1088000000d 0x000dfe1088000000 0xfdfffb18c0000000 0x3fdfffb18c000000

def z369 : W := mkw 0x40200ea00880ec02 0x040200ea00880ec0 0xaf180fe00600fe0a 0xdaf180fe00600fe0

def z370 : W := mkw 0x81ffffdef776000f 0xf81ffffdef776000 0xfdfffffffe600000 0xbfdfffffffe60000

def z371 : W := mkw 0x4800106240812810 0x8480010624081281 0x000430e001830000 0x0000430e00183000

def z372 : W := mkw 0x409402a025802c02 0x2409402a025802c0 0xb51c07e007807e0b 0x5b51c07e007807e0

def z373 : W := mkw 0x80ffec143f76c08c 0x380ffec143f76c08 0x0afb08183e6080c0 0x80afb08183e6080c

def z374 : W := mkw 0x00dfe0000000000c 0x000dfe0000000000 0x08fb000000000000 0x008fb00000000000

def z375 : W := mkw 0x4000002025802c00 0x24000002025802c0 0x0000000007800e02 0x00000000007800e0

def z376 : W := mkw 0x0000104240000000 0x8000010424000000 0xf404f4e7c19f0007 0x7f404f4e7c19f000

def z377 : W := mkw 0x0000000000000000 0x0000000000000000 0xef184b00c6048f3e 0xfef184b00c6048f3

def z378 : W := mkw 0x20628c151858d180 0x120628c151858d18 0xc2038c1f0078f1cc 0x2c2038c1f0078f1c

def z379 : W := mkw 0x81dff15ef776000d 0xf81dff15ef776000 0x7cfff01fffff0007 0xe7cfff01fffff000

def z380 : W := mkw 0x0000000000000000 0x0000000000000000 0xad180b0000000000 0x1ad180b000000000

def z381 : W := mkw 0x00d6800035500000 0x300d680003550000 0x7cff80003ff80007 0xc7cff80003ff8000

def z382 : W := mkw 0x000000002d00c400 0x2000000002d00c40 0x020000003e008600 0x8020000003e00860

def z383 : W := mkw 0x204280011858d180 0x1204280011858d18 0x5ee380003878f1cd 0xc5ee380003878f1c

def z384 : W := mkw 0x0009410880000009 0x0000941088000000 0x40034018c0000000 0x240034018c000000

def z385 : W := mkw 0x20628c151858d180 0x120628c151858d18 0x92e08c1f3818f1c9 0x292e08c1f3818f1c

def z386 : W := mkw 0x2042800110581100 0x1204280011058110 0xdce384073878710d 0xedce384073878710

def z387 : W := mkw 0x1009410882240269 0x0100941088224026 0xef1b4b18c66086c0 0xbef1b4b18c66086c

def z388 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0x31fc07e03f807e03 0x131fc07e03f807e0

def z389 : W := mkw 0x68629c7758d9f990 0x968629c7758d9f99 0xf4e4f4e7f99f793f 0x7f4e4f4e7f99f793

def z390 : W := mkw 0x0000000000000000 0x0000000000000000 0x1004b000019b0001 0x01004b000019b000

def z391 : W := mkw 0x90dfe108b776026d 0x390dfe108b776026 0x7cfff018ffff01f7 0xe7cfff018ffff01f

def z392 : W := mkw 0xa0f6ac153d5ad184 0x3a0f6ac153d5ad18 0x10e4b407399b7001 0x010e4b407399b700

def z393 : W := mkw 0x60b40eb52d88fd82 0x260b40eb52d88fd8 0xbffc0fff3f80ffcb 0xfbffc0fff3f80ffc

def z394 : W := mkw 0x0009410880000009 0x0000941088000000 0x091b0b1800000000 0x0091b0b180000000

def z395 : W := mkw 0x11201fdec0000263 0xc11201fdec000026 0x83000fffc0008ff8 0x383000fffc0008ff

def z396 : W := mkw 0x809d60003776000c 0x3809d60003776000 0x201c70003fff0007 0xc201c70003fff000

def z397 : W := mkw 0x8094200025020004 0x2809420002502000 0x0004300001830000 0x0000430000183000

def z398 : W := mkw 0x2800104340091110 0x8280010434009111 0x00000007c0000130 0x200000007c000013

def z399 : W := mkw 0x2000000100081100 0x0200000010008110 0xde038c1f0078f1cd 0xede038c1f0078f1c

def z400 : W := mkw 0x804be0001276000c 0x1804be0001276000 0x5ce3f000387f0005 0xc5ce3f000387f000

def z401 : W := mkw 0xe8fffee37ffffd1e 0xbe8fffee37ffffd1 0xffffffe7ffffff3f 0xfffffffe7ffffff3

def z402 : W := mkw 0x1000010880000261 0x0100001088000026 0x03000b18000086c0 0x003000b18000086c

def z403 : W := mkw 0x0000000010500000 0x1000000001050000 0x0000000038780005 0xc000000003878000

def z404 : W := mkw 0x1009410882240269 0x0100941088224026 0xed1b4b18c6040e32 0x3ed1b4b18c6040e3

def z405 : W := mkw 0x41201ffec880ec03 0xc41201ffec880ec0 0x83000fffc000fe08 0x383000fffc000fe0

def z406 : W := mkw 0x6800106340893910 0x8680010634089391 0x200470e0c19f793f 0x5200470e0c19f793

def z407 : W := mkw 0x694bf17fc089391d 0xc694bf17fc089391 0xf407f4ffc19f793f 0x7f407f4ffc19f793

def z408 : W := mkw 0x20628c151858d180 0x120628c151858d18 0x12e084073878f1cd 0xc12e084073878f1c

def z409 : W := mkw 0x009d60000000000c 0x0009d60000000000 0x201c700000000000 0x0201c70000000000

def z410 : W := mkw 0x0000000000000000 0x0000000000000000 0x0a030818006080c0 0x80a030818006080c

def z411 : W := mkw 0x0042800010500000 0x1004280001050000 0x7ce7f00039ff0007 0xc7ce7f00039ff000

def z412 : W := mkw 0x409402a025802c02 0x2409402a025802c0 0x000400e001800000 0x0000400e00180000

def z413 : W := mkw 0x90dfe108b776026d 0x390dfe108b776026 0x7ffffb183fff86c7 0xc7ffffb183fff86c

def z414 : W := mkw 0x2000104340081100 0x8200010434008110 0xf404f4e7c018710d 0x7f404f4e7c018710

def z415 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0x3cff00003fe00003 0xc3cff00003fe0000

def z416 : W := mkw 0x909d6108a726026d 0x2909d6108a726026 0x211c7300c7870e32 0x1211c7300c7870e3

def z417 : W := mkw 0x00f68e9400000002 0x000f68e940000000 0xfdff8fff00000000 0x3fdff8fff0000000

def z418 : W := mkw 0x6800106340893910 0x8680010634089391 0xe40044e7c004793e 0x7e40044e7c004793

def z419 : W := mkw 0x00b40e8000000002 0x000b40e800000000 0xbffc0fe006008e0a 0xdbffc0fe006008e0

def z420 : W := mkw 0x1009410882240269 0x0100941088224026 0xe5184300c6040f3e 0x7e5184300c6040f3

def z421 : W := mkw 0x7809412982ad3b79 0x07809412982ad3b7 0xef1b4b18c7ffffff 0xfef1b4b18c7fffff

def z422 : W := mkw 0x60200eb50888fd82 0x060200eb50888fd8 0x83000fff0000ffc8 0x383000fff0000ffc

def z423 : W := mkw 0xa0ffec153f7ed18c 0x3a0ffec153f7ed18 0xdefb8c1f3e78f1cd 0xedefb8c1f3e78f1c

def z424 : W := mkw 0x40ffeea02d80ec0e 0x240ffeea02d80ec0 0xffffffe03f80fe0b 0xdffffffe03f80fe0

def z425 : W := mkw 0x20628c151858d180 0x120628c151858d18 0xfee3cc1ff87cf9ff 0xffee3cc1ff87cf9f

def z426 : W := mkw 0x8000000027260000 0x2800000002726000 0x0000000007870002 0x0000000000787000

def z427 : W := mkw 0x11ffffdec224026f 0xc11ffffdec224026 0xfdffffffc06401f4 0x3fdffffffc06401f

def z428 : W := mkw 0x0009514ac0000009 0x80009514ac000000 0xfd1fffffc0000000 0x3fd1fffffc000000

def z429 : W := mkw 0x3809514bc22d1379 0x83809514bc22d137 0x4003f01fc07f01f4 0x24003f01fc07f01f

def z430 : W := mkw 0xc0dfe02037f6280c 0x3c0dfe02037f6280 0xfcfff4e03fff780f 0xdfcfff4e03fff780

def z431 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xffffffffc6008e0a 0xfffffffffc6008e0

def z432 : W := mkw 0x21ffffdfc808d18f 0xc21ffffdfc808d18 0xffffffffc000f1c8 0x3ffffffffc000f1c

def z433 : W := mkw 0x40200ea02d80ec02 0x240200ea02d80ec0 0x83000fe03f80fe0b 0xd83000fe03f80fe0

def z434 : W := mkw 0x304bc11d927c13e9 0x1304bc11d927c13e 0xef1bcb1fc67c8ffe 0xfef1bcb1fc67c8ff

def z435 : W := mkw 0x400002a000802c02 0x0400002a000802c0 0x010003e000000e00 0x1010003e000000e0

def z436 : W := mkw 0x01fffed64000000e 0xc01fffed64000000 0x7cfff4e700000000 0x07cfff4e70000000

def z437 : W := mkw 0x81f6bed675520006 0xf81f6bed67552000 0x10e4b4e7399b0001 0x010e4b4e7399b000

def z438 : W := mkw 0x104bc10892740269 0x1104bc1089274026 0xfffbcb18fe7c8fff 0xffffbcb18fe7c8ff

def z439 : W := mkw 0x20f68c153d58d180 0x320f68c153d58d18 0xfeff8c1f3ff8f1cf 0xefeff8c1f3ff8f1c

def z440 : W := mkw 0x69f6bef740893916 0xc69f6bef74089391 0xf4e4f4e7c19f793f 0x7f4e4f4e7c19f793

def z441 : W := mkw 0x30294d1d8a2cd3e9 0x030294d1d8a2cd3e 0xef1b4f1fc664fffe 0xfef1b4f1fc664fff

def z442 : W := mkw 0x204280151858d180 0x1204280151858d18 0x4203801f3878f1cd 0xe4203801f3878f1c

def z443 : W := mkw 0x500000202fa4ee60 0x2500000202fa4ee6 0x020000003fe4ffff 0xc020000003fe4fff

def z444 : W := mkw 0x1009410882240269 0x0100941088224026 0x4b1b4b18c66487f4 0xa4b1b4b18c66487f

def z445 : W := mkw 0x8009400037760008 0x3800940003776000 0x6c1b40003fff0007 0xc6c1b40003fff000

def z446 : W := mkw 0x0100115ec0000001 0xc0100115ec000000 0x0000001fc0000000 0x20000001fc000000

def z447 : W := mkw 0x68201ee34889fd12 0x868201ee34889fd1 0x83000fe7c000ff38 0x383000fe7c000ff3

def z448 : W := mkw 0x409402a025802c02 0x2409402a025802c0 0x3dfc03e03f800e03 0xd3dfc03e03f800e0

def z449 : W := mkw 0x00628c001850c000 0x100628c001850c00 0xdee38c003878f00d 0xcdee38c003878f00

def z450 : W := mkw 0x68b41ee340893912 0x868b41ee34089391 0xfdfcffe7c19f793f 0x7fdfcffe7c19f793

def z451 : W := mkw 0x0000000000000000 0x0000000000000000 0xef1b0b1806608fce 0xfef1b0b1806608fc

def z452 : W := mkw 0x0000000000000000 0x0000000000000000 0x20004000c0040832 0x120004000c004083

def z453 : W := mkw 0xe8d6b06375db3914 0xbe8d6b06375db391 0xf4e4f4e7f99f793f 0x7f4e4f4e7f99f793

def z454 : W := mkw 0x00b40c002d00c000 0x200b40c002d00c00 0xbefc0c003f80f00b 0xcbefc0c003f80f00

def z455 : W := mkw 0x1009410882240269 0x0100941088224026 0xed1b4b18c06401f4 0x3ed1b4b18c06401f

def z456 : W := mkw 0x78bd5febefadff7b 0xa78bd5febefadff7 0xffffffffffffffff 0xffffffffffffffff

def z457 : W := mkw 0x109d4108a7240269 0x2109d4108a724026 0xffff4b18ffe48fff 0xfffff4b18ffe48ff

def z458 : W := mkw 0x20200c150808d180 0x020200c150808d18 0xd6008c1f0018f1cd 0x6d6008c1f0018f1c

def z459 : W := mkw 0x0000000000000000 0x0000000000000000 0xe4004000c0000000 0x3e4004000c000000

def z460 : W := mkw 0x8000000037760000 0x3800000003776000 0x7404f0003fff0007 0xc7404f0003fff000

def z461 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0x30fcf0003f9f0003 0x030fcf0003f9f000

def z462 : W := mkw 0x68629c7758d9f990 0x968629c7758d9f99 0xdee7bcff39fbf1cd 0xedee7bcff39fbf1c

def z463 : W := mkw 0x0000000000000000 0x0000000000000000 0xa40000000000080a 0x5a40000000000080

def z464 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0xb4e404e03980780b 0x5b4e404e03980780

def z465 : W := mkw 0x80ffee803776000e 0x380ffee803776000 0xfdffffe03fff0007 0xdfdffffe03fff000

def z466 : W := mkw 0x0000000000000000 0x0000000000000000 0x40004000c0040134 0x240004000c004013

def z467 : W := mkw 0x019432c240000006 0xc019432c24000000 0x000430e000000000 0x0000430e00000000

def z468 : W := mkw 0x20628c151858d180 0x120628c151858d18 0x1ae38c1f3878f0c1 0x81ae38c1f3878f0c

def z469 : W := mkw 0x00200c140800c080 0x000200c140800c08 0x02000818000080c0 0x002000818000080c

def z470 : W := mkw 0x40b40ea025802c02 0x240b40ea025802c0 0xbdfc0fe007800e02 0x1bdfc0fe007800e0

def z471 : W := mkw 0x60f68eb53dd8fd82 0x360f68eb53dd8fd8 0xdee78cff39f8f1cd 0xedee78cff39f8f1c

def z472 : W := mkw 0x00bd4f888000000b 0x000bd4f888000000 0xfdff4ff8c0000000 0x3fdff4ff8c000000

def z473 : W := mkw 0x21ffffdfc008110f 0xc21ffffdfc008110 0xfdffffffc018710d 0x7fdffffffc018710

def z474 : W := mkw 0x0000000000000000 0x0000000000000000 0xc40000000000010c 0x6c40000000000010

def z475 : W := mkw 0x819d73cae726000f 0xe819d73cae726000 0x211c73e0c7870002 0x1211c73e0c787000

def z476 : W := mkw 0x680010636d89fd10 0xa680010636d89fd1 0xf604f4e7ff9fff3f 0xff604f4e7ff9fff3

def z477 : W := mkw 0x1009410882240269 0x0100941088224026 0x611b4318c6640ff6 0x3611b4318c6640ff

def z478 : W := mkw 0x60628eb518d8fd82 0x160628eb518d8fd8 0xdfe38fff3878ffcd 0xfdfe38fff3878ffc

def z479 : W := mkw 0x20f68e951858d182 0x120f68e951858d18 0xffff8fff3878f1cd 0xfffff8fff3878f1c

def z480 : W := mkw 0x00dfe0001050000c 0x100dfe0001050000 0x7cfff00038780005 0xc7cfff0003878000

def z481 : W := mkw 0x2042801510581180 0x1204280151058118 0xce03881f007881cc 0xece03881f007881c

def z482 : W := mkw 0x1000010880000261 0x0100001088000026 0xaf180b18c6008ffa 0xfaf180b18c6008ff

def z483 : W := mkw 0xc00000203ff6ec00 0x3c00000203ff6ec0 0x020000003ffffe0f 0xc020000003ffffe0

def z484 : W := mkw 0x1009400002240268 0x0100940000224026 0x6e1b400006648ffe 0xc6e1b400006648ff

def z485 : W := mkw 0x2000000100081100 0x0200000010008110 0xf400c407c01c793f 0x7f400c407c01c793

def z486 : W := mkw 0xe8dff06377ff391c 0xbe8dff06377ff391 0x7cfff4e73fff7007 0xc7cfff4e73fff700

def z487 : W := mkw 0x48b41ee26d81ec12 0xa48b41ee26d81ec1 0xbffc7fe0ff87fe3b 0xdbffc7fe0ff87fe3

def z488 : W := mkw 0x904be1089276026d 0x1904be1089276026 0xef1bfb18c67f8ffe 0xfef1bfb18c67f8ff

def z489 : W := mkw 0x2000001500081180 0x0200000150008118 0x0000001f000001c0 0x20000001f000001c

def z490 : W := mkw 0x014bf15ec000000d 0xc014bf15ec000000 0xf407f4ffc0000000 0x3f407f4ffc000000

def z491 : W := mkw 0x600000213dd8fd80 0x3600000213dd8fd8 0x020000003ff8ffcf 0xc020000003ff8ffc

def z492 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0x48fbf0003e7f0004 0x848fbf0003e7f000

def z493 : W := mkw 0x01b41fdec0000003 0xc01b41fdec000000 0xbdfc0fffc0000000 0x3bdfc0fffc000000

def z494 : W := mkw 0x106bcd1c9a74c2e9 0x1106bcd1c9a74c2e 0x0bfb0b183e6086c0 0x80bfb0b183e6086c

def z495 : W := mkw 0x21201fdfc808d183 0xc21201fdfc808d18 0x83000fffc000f1c8 0x383000fffc000f1c

def z496 : W := mkw 0x294bf15fc009111d 0xc294bf15fc009111 0x4003f01fc01f0134 0x24003f01fc01f013

def z497 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0x6cfb40003e640006 0xc6cfb40003e64000

def z498 : W := mkw 0x6800106340893910 0x8680010634089391 0x1004b4e7019f793f 0x41004b4e7019f793

def z499 : W := mkw 0x90dfe0003776026c 0x390dfe0003776026 0x7efff0003fff8fff 0xc7efff0003fff8ff

def z500 : W := mkw 0x00b40e8000000002 0x000b40e800000000 0x09f80b0000000000 0x009f80b000000000

def z501 : W := mkw 0x0000104240000000 0x8000010424000000 0x4000f007c0000000 0x24000f007c000000

def z502 : W := mkw 0x41fffffee5802c0f 0xe41fffffee5802c0 0xfdffffffc7800e02 0x3fdffffffc7800e0

def z503 : W := mkw 0x30094109822c1369 0x030094109822c136 0xff1bcf1fc67cffff 0xfff1bcf1fc67cfff

def z504 : W := mkw 0x1000000002240260 0x0100000000224026 0xce03081806648ffe 0xece03081806648ff

def z505 : W := mkw 0xc0b40ea03ff6ec02 0x3c0b40ea03ff6ec0 0xbffc0fe03ffffe0f 0xdbffc0fe03ffffe0

def z506 : W := mkw 0x20f68e953d58d582 0x320f68e953d58d58 0xdffb8f1f3e78f7cd 0xedffb8f1f3e78f7c

def z507 : W := mkw 0x114bf15ec224026d 0xc114bf15ec224026 0xef1bfb1fc6648ffe 0xfef1bfb1fc6648ff

def z508 : W := mkw 0x00200c000800c000 0x000200c000800c00 0xbff80f003e00fe0b 0xdbff80f003e00fe0

def z509 : W := mkw 0x1000010880000261 0x0100001088000026 0x00000018c00001f0 0x200000018c00001f

def z510 : W := mkw 0x40bd4ea02fa4ec0a 0x240bd4ea02fa4ec0 0xffff4fe03fe4fe0f 0xdffff4fe03fe4fe0

def z511 : W := mkw 0x28629c575859d190 0x928629c575859d19 0xdee3fc1ff87ff1fd 0xedee3fc1ff87ff1f

def z512 : W := mkw 0x400000202d80ec00 0x2400000202d80ec0 0xaf180b003f80fe0b 0xdaf180b003f80fe0

def z513 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0x3cfc04e03f807003 0xc3cfc04e03f80700

def z514 : W := mkw 0x4000002000802800 0x0400000200080280 0x000000000180780b 0x4000000000180780

def z515 : W := mkw 0x0009410880000009 0x0000941088000000 0xed1b4b18c004093e 0x7ed1b4b18c004093

def z516 : W := mkw 0x400000200880ec00 0x0400000200880ec0 0x020000000000fe08 0x0020000000000fe0

def z517 : W := mkw 0x81ffffded276000f 0xd81ffffded276000 0xfdffffffc07f0004 0x3fdffffffc07f000

def z518 : W := mkw 0x016bfd5ec000000d 0xc016bfd5ec000000 0xdce3fc1fc0000000 0x2dce3fc1fc000000

def z519 : W := mkw 0xa0628c153f7ed180 0x3a0628c153f7ed18 0xdee38c1f3ffff1cf 0xedee38c1f3ffff1c

def z520 : W := mkw 0x30628d1d9858d3e1 0x130628d1d9858d3e 0xdfe38f1ff878fffd 0xfdfe38f1ff878fff

def z521 : W := mkw 0x0042801400000000 0x0004280140000000 0x4003801f00000000 0x24003801f0000000

def z522 : W := mkw 0xe8dfe02137ff391c 0x3e8dfe02137ff391 0x7cfff0003fff793f 0xc7cfff0003fff793

def z523 : W := mkw 0x20628c151858d180 0x120628c151858d18 0xd4e084073818710d 0x6d4e084073818710

def z524 : W := mkw 0x0000000000000000 0x0000000000000000 0x40030018006001c4 0x240030018006001c

def z525 : W := mkw 0x4000002000802800 0x0400000200080280 0xbf1c0fe00780fe0b 0xdbf1c0fe00780fe0

def z526 : W := mkw 0x40f68ea03dd0ec02 0x340f68ea03dd0ec0 0xffff8fe03ff8fe0f 0xdffff8fe03ff8fe0

def z527 : W := mkw 0x0000000000000000 0x0000000000000000 0xee034818c06489fe 0xfee034818c06489f

def z528 : W := mkw 0x40200c200880e800 0x040200c200880e80 0xbee40ce03980f80b 0xdbee40ce03980f80

def z529 : W := mkw 0xa0dfe015377e118c 0x3a0dfe015377e118 0x7cfff01f3fff01c7 0xe7cfff01f3fff01c

def z530 : W := mkw 0x50094128afa4ee69 0x250094128afa4ee6 0xef1b4b18ffe4ffff 0xfef1b4b18ffe4fff

def z531 : W := mkw 0x1000000000000260 0x0100000000000026 0x0200000000008ff8 0x00200000000008ff

def z532 : W := mkw 0x01dff3cac000000f 0xc01dff3cac000000 0x7dfff3e0c0000000 0x17dfff3e0c000000

def z533 : W := mkw 0x41fffffec080280f 0xc41fffffec080280 0xfdffffffc180780b 0x7fdffffffc180780

def z534 : W := mkw 0x0042801410500080 0x1004280141050008 0x00030018006000c0 0x000030018006000c

def z535 : W := mkw 0x0009400002240008 0x0000940000224000 0x2018400006040002 0x0201840000604000

def z536 : W := mkw 0x4800106240812810 0x8480010624081281 0xf404f4e7c1870832 0x3f404f4e7c187083

def z537 : W := mkw 0x2800104340091110 0x8280010434009111 0x7404f007c19f0137 0x67404f007c19f013

def z538 : W := mkw 0x1009410882240269 0x0100941088224026 0x42034018c6648ffe 0xe42034018c6648ff

def z539 : W := mkw 0x20628c151858d180 0x120628c151858d18 0x9ee08c073818f009 0xc9ee08c073818f00

def z540 : W := mkw 0x114bf15ec224026d 0xc114bf15ec224026 0x4003f01fc06401f4 0x24003f01fc06401f

def z541 : W := mkw 0x69ffffffd8d9f99f 0xd69ffffffd8d9f99 0xfffffffff9fff9ff 0xffffffffff9fff9f

def z542 : W := mkw 0x699d73ebc089391f 0xc699d73ebc089391 0xf51cf7e7c19f793f 0x7f51cf7e7c19f793

def z543 : W := mkw 0x0000104240000000 0x8000010424000000 0xf404f4e7c004093e 0x7f404f4e7c004093

def z544 : W := mkw 0xa00000013f7ed180 0x3a00000013f7ed18 0x020000003ffff1cf 0xc020000003ffff1c

def z545 : W := mkw 0x304bc11d927c13e9 0x1304bc11d927c13e 0x4003c01fc07c01f4 0x24003c01fc07c01f

def z546 : W := mkw 0x6800106340893910 0x8680010634089391 0xd404b4e7019b710d 0x6d404b4e7019b710

def z547 : W := mkw 0x1009410882240269 0x0100941088224026 0xa3184b18c6048ffa 0x3a3184b18c6048ff

def z548 : W := mkw 0x69ffffffc089391f 0xc69ffffffc089391 0xfdffffffc0007938 0x3fdffffffc000793

def z549 : W := mkw 0x409402a02d80ec02 0x2409402a02d80ec0 0x231c03e03f80fe0b 0xd231c03e03f80fe0

def z550 : W := mkw 0x2800104340091110 0x8280010434009111 0x0000b007001b0000 0x00000b007001b000

def z551 : W := mkw 0x7800106342ad3b70 0x87800106342ad3b7 0xf604f4e7c7ffffff 0xff604f4e7c7fffff

def z552 : W := mkw 0xe0ffeeb53ffefd8e 0x3e0ffeeb53ffefd8 0xffffffff3fffffcf 0xfffffffff3fffffc

def z553 : W := mkw 0x0042800000000000 0x0004280000000000 0x5ce3800000000000 0x05ce380000000000

def z554 : W := mkw 0x40200c202d80ec00 0x240200c202d80ec0 0x9ee00c003f80fe0b 0xc9ee00c003f80fe0

def z555 : W := mkw 0xa0dfe001377e110c 0x3a0dfe001377e110 0xfcfff4073fff710f 0xefcfff4073fff710

def z556 : W := mkw 0x0009400002240008 0x0000940000224000 0x081b000006600000 0x8081b00000660000

def z557 : W := mkw 0x1009410882240269 0x0100941088224026 0xe4034018c06409fe 0x7e4034018c06409f

def z558 : W := mkw 0x68f69ef77dd9fd92 0xb68f69ef77dd9fd9 0xffffffffffffffff 0xffffffffffffffff

def z559 : W := mkw 0x68b41ee36d89fd12 0xa68b41ee36d89fd1 0x10e4b4e7399b7001 0x010e4b4e7399b700

def z560 : W := mkw 0x50bd4fa8afa4ee6b 0x250bd4fa8afa4ee6 0xbffc4fe0ff84fe3b 0xdbffc4fe0ff84fe3

def z561 : W := mkw 0x1009410882240269 0x0100941088224026 0x0118030006000600 0x0011803000600060

def z562 : W := mkw 0x904be1089276026d 0x1904be1089276026 0x4003f018c07f01f4 0x24003f018c07f01f

def z563 : W := mkw 0x800960000226000c 0x0800960000226000 0x0000700000070000 0x0000070000007000

def z564 : W := mkw 0x804be0003776000c 0x3804be0003776000 0x4003f0003fff0007 0xc4003f0003fff000

def z565 : W := mkw 0x4000002000802800 0x0400000200080280 0x100404e001807001 0x0100404e00180700

def z566 : W := mkw 0x2000000100081100 0x0200000010008110 0x4000800700180104 0x2400080070018010

def z567 : W := mkw 0x60b40ea12d88fd02 0x260b40ea12d88fd0 0xfffc8fe73f98ff0f 0xffffc8fe73f98ff0

def z568 : W := mkw 0x0009400002240008 0x0000940000224000 0xef1b4b0006648e0e 0xdef1b4b0006648e0

def z569 : W := mkw 0x68628c3518d9f990 0x168628c3518d9f99 0xdee38c1f39fff9ff 0xedee38c1f39fff9f

def z570 : W := mkw 0x6800002100893910 0x0680000210089391 0xb40404e0019f793f 0x5b40404e0019f793

def z571 : W := mkw 0x0000000000000000 0x0000000000000000 0x1ce0000038000001 0xc1ce000003800000

def z572 : W := mkw 0x68b40ea12d89fd12 0x268b40ea12d89fd1 0xbffc0fe03f9fff3f 0xdbffc0fe03f9fff3

def z573 : W := mkw 0x20200c151858d180 0x120200c151858d18 0x82000c1f3878f1cd 0xe82000c1f3878f1c

def z574 : W := mkw 0x2800104340091110 0x8280010434009111 0xe400f007c01f093e 0x7e400f007c01f093

def z575 : W := mkw 0x01ffffdec224000f 0xc01ffffdec224000 0xfdffffffc6640006 0xffdffffffc664000

def z576 : W := mkw 0x00200c000800c000 0x000200c000800c00 0x10e0040038007001 0x010e004003800700

def z577 : W := mkw 0x200000011858d180 0x1200000011858d18 0xce0308183878f1cd 0xece0308183878f1c

def z578 : W := mkw 0x0142b05640000004 0xc0142b0564000000 0x0000b00700000000 0x00000b0070000000

def z579 : W := mkw 0xe8fffc777ffff99c 0xbe8fffc777ffff99 0xfefffcfffffff9ff 0xffefffcfffffff9f

def z580 : W := mkw 0x014be11c8000000d 0x4014be11c8000000 0x0003001800000000 0x0000300180000000

def z581 : W := mkw 0xe8d6b06375db3914 0xbe8d6b06375db391 0x10e4b4e7399b7001 0x010e4b4e7399b700

def z582 : W := mkw 0x006bcd1c80000009 0x0006bcd1c8000000 0xfdfbcf1fc0000000 0x3fdfbcf1fc000000

def z583 : W := mkw 0x68b41ee36d89fd12 0xa68b41ee36d89fd1 0xbffcbfe73f9bfe0b 0xdbffcbfe73f9bfe0

def z584 : W := mkw 0x6800106340893910 0x8680010634089391 0x7404f4e7019f7007 0x47404f4e7019f700

def z585 : W := mkw 0xc89d706267a7281c 0xac89d706267a7281 0x201c70e0c7870832 0x1201c70e0c787083

def z586 : W := mkw 0x50b40ea02fa4ee62 0x250b40ea02fa4ee6 0xbffc0fe03fe4ffff 0xdbffc0fe03fe4fff

def z587 : W := mkw 0x1009410882240269 0x0100941088224026 0xce034818c06481fc 0xece034818c06481f

def z588 : W := mkw 0x60628c3518d8f980 0x160628c3518d8f98 0xfee78cff39f8f9cf 0xffee78cff39f8f9c

def z589 : W := mkw 0x20628c151858d180 0x120628c151858d18 0x4ae3881f387881c4 0xa4ae3881f387881c

def z590 : W := mkw 0x20ffec151858d18c 0x120ffec151858d18 0xfefffc1f3878f1cd 0xefefffc1f3878f1c

def z591 : W := mkw 0xa84bf043527f111c 0x9a84bf043527f111 0x4003f007c07f0134 0x24003f007c07f013

def z592 : W := mkw 0x01dff15ec000000d 0xc01dff15ec000000 0x7cfff01fc0000000 0x27cfff01fc000000

def z593 : W := mkw 0x4000002000802800 0x0400000200080280 0xf40444e0c184793f 0x7f40444e0c184793

def z594 : W := mkw 0x119d73cac224026f 0xc119d73cac224026 0xef1f7bf8c6648ffe 0xfef1f7bf8c6648ff

def z595 : W := mkw 0x20200c011858d180 0x120200c011858d18 0x9ee00c003878f1cd 0xc9ee00c003878f1c

def z596 : W := mkw 0x499d73eac081281f 0xc499d73eac081281 0x211c73e0c1870832 0x1211c73e0c187083

def z597 : W := mkw 0x206bcd1d9858d189 0x1206bcd1d9858d18 0xfffbcf1ff878f1cd 0xffffbcf1ff878f1c

def z598 : W := mkw 0x0009400002240008 0x0000940000224000 0xee1b4818066481ce 0xeee1b4818066481c

def z599 : W := mkw 0x4000002000802800 0x0400000200080280 0x800004e000007808 0x1800004e00000780

def z600 : W := mkw 0x809d60002726000c 0x2809d60002726000 0x6c1f700007e70006 0xc6c1f700007e7000

def z601 : W := mkw 0x2042801510581180 0x1204280151058118 0xd403841f007871cd 0x6d403841f007871c

def z602 : W := mkw 0x68201ee34889fd12 0x868201ee34889fd1 0xf704ffe7c19fff3f 0x7f704ffe7c19fff3

def z603 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0x12e404e03f80fe0b 0xc12e404e03f80fe0

def z604 : W := mkw 0x41f6bef66d80ec06 0xe41f6bef66d80ec0 0xbffcbfe73f80fe0b 0xdbffcbfe73f80fe0

def z605 : W := mkw 0x0009410882240009 0x0000941088224000 0xed1b4b18c6640006 0xfed1b4b18c664000

def z606 : W := mkw 0x00628c141850c080 0x100628c141850c08 0x5ee38818387880c5 0xc5ee38818387880c

def z607 : W := mkw 0x00dfe0000000000c 0x000dfe0000000000 0x7cfff000019f0007 0x47cfff000019f000

def z608 : W := mkw 0x106bcd1c82240269 0x0106bcd1c8224026 0xfffbcf1fc6648ffe 0xffffbcf1fc6648ff

def z609 : W := mkw 0x4800002000812810 0x0480000200081281 0x0000000001870832 0x0000000000187083

def z610 : W := mkw 0x00b40e802d00c402 0x200b40e802d00c40 0xaff80b003e008e0a 0xdaff80b003e008e0

def z611 : W := mkw 0x4094002025802800 0x2409400202580280 0xbcfc04e03f80780b 0xdbcfc04e03f80780

def z612 : W := mkw 0x7800116bc0893b71 0x87800116bc0893b7 0x83000fffc000fff8 0x383000fffc000fff

def z613 : W := mkw 0x68dff0634089391c 0x868dff0634089391 0xfcfff4e7c19f793f 0x7fcfff4e7c19f793

def z614 : W := mkw 0xe84bf06352ff391c 0x9e84bf06352ff391 0xf407f4e7c1ff793f 0x7f407f4e7c1ff793

def z615 : W := mkw 0xe89d706367af391c 0xae89d706367af391 0xf41cf4e7c79f793f 0x7f41cf4e7c79f793

def z616 : W := mkw 0x2800104340091110 0x8280010434009111 0xf404f4e7c01f0134 0x3f404f4e7c01f013

def z617 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0x2bfc0be03f808e02 0x92bfc0be03f808e0

def z618 : W := mkw 0xc0bd6ea02fa6ec0e 0x2c0bd6ea02fa6ec0 0xbffc7fe03f87fe0b 0xdbffc7fe03f87fe0

def z619 : W := mkw 0xc09d62a027a62c0e 0x2c09d62a027a62c0 0x211c73e007870e02 0x1211c73e007870e0

def z620 : W := mkw 0x0009400000000008 0x0000940000000000 0x6c1b400000000000 0x06c1b40000000000

def z621 : W := mkw 0x30628c151a7cd3e0 0x130628c151a7cd3e 0xdee38c1f3e7cffff 0xedee38c1f3e7cfff

def z622 : W := mkw 0x20628c150808d180 0x020628c150808d18 0xdee38c1f0000f1c8 0x2dee38c1f0000f1c

def z623 : W := mkw 0x0000000000000000 0x0000000000000000 0x2c18000006000002 0xc2c1800000600000

def z624 : W := mkw 0x689412e365893d12 0xa689412e365893d1 0xf51cf7e7c79f7f3f 0x7f51cf7e7c79f7f3

def z625 : W := mkw 0x1000010880000261 0x0100001088000026 0xcf030b18c0608ffc 0xfcf030b18c0608ff

def z626 : W := mkw 0x41bd7feaed80ec0f 0xe41bd7feaed80ec0 0xbffc7fe0ff80fe0b 0xdbffc7fe0ff80fe0

def z627 : W := mkw 0x804be0001276000c 0x1804be0001276000 0x6c1bf000067f0006 0xc6c1bf000067f000

def z628 : W := mkw 0x50294fa88aa4ee6b 0x050294fa88aa4ee6 0xef1b4ff8c664fffe 0xfef1b4ff8c664fff

def z629 : W := mkw 0x10bd4f88af24c66b 0x210bd4f88af24c66 0xeffb4b18fe648ffe 0xfeffb4b18fe648ff

def z630 : W := mkw 0x0000000002240000 0x0000000000224000 0x0000000006640006 0xc000000000664000

def z631 : W := mkw 0x0009400002240008 0x0000940000224000 0x4003400000640004 0x0400340000064000

def z632 : W := mkw 0x20628c1500081100 0x020628c150008110 0xdce38c1f0018710d 0x6dce38c1f0018710

def z633 : W := mkw 0x0000000000000000 0x0000000000000000 0x6400400000040006 0x4640040000004000

def z634 : W := mkw 0x0109714ac000000d 0xc0109714ac000000 0x00007000c0000000 0x000007000c000000

def z635 : W := mkw 0x81dff3caf776000f 0xf81dff3caf776000 0x7dfff3e0ffff0007 0xd7dfff3e0ffff000

def z636 : W := mkw 0x004be0000000000c 0x0004be0000000000 0x4003f00000000000 0x04003f0000000000

def z637 : W := mkw 0x5809516ac2a52a79 0x85809516ac2a52a7 0x211c73e0c7870e32 0x1211c73e0c7870e3

def z638 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0xa31c0fe00780fe0a 0x1a31c0fe00780fe0

def z639 : W := mkw 0x0000000025000000 0x2000000002500000 0x000000003f800003 0xc000000003f80000

def z640 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0x9ee40ce03980f009 0xc9ee40ce03980f00

def z641 : W := mkw 0x29ffffdfc009111f 0xc29ffffdfc009111 0xfdffffffc01f0134 0x3fdffffffc01f013

def z642 : W := mkw 0x00628c140800c000 0x000628c140800c00 0xdee38c1f3800f009 0xedee38c1f3800f00

def z643 : W := mkw 0x1000000002240260 0x0100000000224026 0xe6004000c6648ffe 0xfe6004000c6648ff

def z644 : W := mkw 0x4800106240812810 0x8480010624081281 0xb40474e0c187783b 0x5b40474e0c187783

def z645 : W := mkw 0x5009412882a42a69 0x05009412882a42a6 0xff1f4ff8c7e4ffff 0xfff1f4ff8c7e4fff

def z646 : W := mkw 0x0000000000000000 0x0000000000000000 0x3404000001800003 0x4340400000180000

def z647 : W := mkw 0x00200c000800c000 0x000200c000800c00 0xdee30c183860f1cd 0xedee30c183860f1c

def z648 : W := mkw 0x11ffef9c8224026f 0x411ffef9c8224026 0x0bfb0b18066086c0 0x80bfb0b18066086c

def z649 : W := mkw 0x0000000000000000 0x0000000000000000 0x4c03000000600004 0xc4c0300000060000

def z650 : W := mkw 0x1009410882240269 0x0100941088224026 0xaf1b0b1806608eca 0xdaf1b0b1806608ec

def z651 : W := mkw 0x01ffef9c8000000f 0x401ffef9c8000000 0xbdff0ff800000000 0x1bdff0ff80000000

def z652 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0x5cfb80003e780005 0xc5cfb80003e78000

def z653 : W := mkw 0x00628c141850c080 0x100628c141850c08 0x9ee30c183860f0c9 0xc9ee30c183860f0c

def z654 : W := mkw 0x6800106340893910 0x8680010634089391 0x9004b4e7c19b7939 0x39004b4e7c19b793

def z655 : W := mkw 0x40200ea00880ec02 0x040200ea00880ec0 0x9fe00fe03800fe09 0xd9fe00fe03800fe0

def z656 : W := mkw 0x40b40ea000802802 0x040b40ea00080280 0xbdfc0fe00180780b 0x5bdfc0fe00180780

def z657 : W := mkw 0x90094108b7760269 0x390094108b776026 0xef1b4b18ffff8fff 0xfef1b4b18ffff8ff

def z658 : W := mkw 0x004bc00012740008 0x1004bc0001274000 0x7cfbc0003e7c0007 0xc7cfbc0003e7c000

def z659 : W := mkw 0x68629c7758d9f990 0x968629c7758d9f99 0xdee38cfff878f9fd 0xfdee38cfff878f9f

def z660 : W := mkw 0x8094000037760000 0x3809400003776000 0x3cfc00003fff0007 0xc3cfc00003fff000

def z661 : W := mkw 0x0000000000000000 0x0000000000000000 0x83000b0000008e08 0x183000b0000008e0

def z662 : W := mkw 0x01ffef9c8000000f 0x401ffef9c8000000 0xddfb8f1f00000000 0x2ddfb8f1f0000000

def z663 : W := mkw 0x804be0001276000c 0x1804be0001276000 0x0003000000600000 0x0000300000060000

def z664 : W := mkw 0xa0dfe0013f7ed18c 0x3a0dfe0013f7ed18 0x7efff0003ffff1cf 0xc7efff0003ffff1c

def z665 : W := mkw 0x1009410882240269 0x0100941088224026 0x00030018006000c0 0x000030018006000c

def z666 : W := mkw 0x00f68e943d50c482 0x300f68e943d50c48 0x0bfb0b183e6086c0 0x80bfb0b183e6086c

def z667 : W := mkw 0x214bf15fd058118d 0xd214bf15fd058118 0x4003f01fc07801c4 0x24003f01fc07801c

def z668 : W := mkw 0x60f68eb53dd8fd82 0x360f68eb53dd8fd8 0xbffc8fe73f98fe0b 0xdbffc8fe73f98fe0

def z669 : W := mkw 0x6800106340893910 0x8680010634089391 0x4000f007c19f793f 0x64000f007c19f793

def z670 : W := mkw 0x00b40e802d00c402 0x200b40e802d00c40 0x00e0000038000000 0x000e000003800000

def z671 : W := mkw 0x30200d1d8808d3e1 0x030200d1d8808d3e 0x83000f1fc000fff8 0x383000f1fc000fff

def z672 : W := mkw 0x1009410882240269 0x0100941088224026 0xc3034b18c0648ffc 0x3c3034b18c0648ff

def z673 : W := mkw 0x00200c000800c000 0x000200c000800c00 0x0ae0080038008000 0x80ae008003800800

def z674 : W := mkw 0x0000000000000000 0x0000000000000000 0x5400800000180005 0x4540080000018000

def z675 : W := mkw 0x019d73cac000000f 0xc019d73cac000000 0xed1f7bf8c0000000 0x3ed1f7bf8c000000

def z676 : W := mkw 0xc0dfe0203ff6ec0c 0x3c0dfe0203ff6ec0 0x7efff0003ffffe0f 0xc7efff0003ffffe0

def z677 : W := mkw 0x509d43a8a7a42e6b 0x2509d43a8a7a42e6 0x211c43e0c7840e32 0x1211c43e0c7840e3

def z678 : W := mkw 0x2000000100081100 0x0200000010008110 0x1000840700187001 0x0100084070018700

def z679 : W := mkw 0x489412e265812c12 0xa489412e265812c1 0x211c73e0c7870e32 0x1211c73e0c7870e3

def z680 : W := mkw 0x7809516bc2ad3b79 0x87809516bc2ad3b7 0xf407f4ffc1ff79ff 0x7f407f4ffc1ff79f

def z681 : W := mkw 0x10bd4f888224026b 0x010bd4f888224026 0xffff4ff8c6648ffe 0xfffff4ff8c6648ff

def z682 : W := mkw 0x7800116bc0893b71 0x87800116bc0893b7 0xf704ffffc19fffff 0x7f704ffffc19ffff

def z683 : W := mkw 0x68b41ee36d89fd12 0xa68b41ee36d89fd1 0xf4e4f4e7f99f793f 0x7f4e4f4e7f99f793

def z684 : W := mkw 0x0009410880000009 0x0000941088000000 0x21184300c0000000 0x121184300c000000

def z685 : W := mkw 0x69201fffc0893913 0xc69201fffc089391 0x81000fffc0007938 0x381000fffc000793

def z686 : W := mkw 0x786bdd7fdafdfbf9 0x9786bdd7fdafdfbf 0xffffffffffffffff 0xffffffffffffffff

def z687 : W := mkw 0x009d400027240008 0x2009d40002724000 0x7cff40003fe40007 0xc7cff40003fe4000

def z688 : W := mkw 0x7809516bc2ad3b79 0x87809516bc2ad3b7 0xf51cf7e7c79f7f3f 0x7f51cf7e7c79f7f3

def z689 : W := mkw 0x6800106340893910 0x8680010634089391 0xb404b4e7019b780b 0x5b404b4e7019b780

def z690 : W := mkw 0x0000000000000000 0x0000000000000000 0xcc03081800000000 0x2cc0308180000000

def z691 : W := mkw 0x206bcc151a7cd188 0x1206bcc151a7cd18 0xfefbcc1f3e7cf1cf 0xefefbcc1f3e7cf1c

def z692 : W := mkw 0x01bd7fcac000000f 0xc01bd7fcac000000 0xbdfc7fe0c0000000 0x1bdfc7fe0c000000

def z693 : W := mkw 0x2000000100081100 0x0200000010008110 0x8000040700007108 0x2800004070000710

def z694 : W := mkw 0x00ffee800000000e 0x000ffee800000000 0xfdffffe000000000 0x1fdffffe00000000

def z695 : W := mkw 0x00dfe0002500000c 0x200dfe0002500000 0x7cfff0003f800003 0xc7cfff0003f80000

def z696 : W := mkw 0xc0dfe2a037f62c0e 0x3c0dfe2a037f62c0 0x7dfff3e03fff0e07 0xd7dfff3e03fff0e0

def z697 : W := mkw 0x0094028000000002 0x0009402800000000 0x211c03e000000000 0x1211c03e00000000

def z698 : W := mkw 0x0000000000000000 0x0000000000000000 0x82000818000081c8 0x282000818000081c

def z699 : W := mkw 0x01ffef9c9850c08f 0x501ffef9c9850c08 0x0bfb0b18386080c0 0x80bfb0b18386080c

def z700 : W := mkw 0x21ffffdfd858d18f 0xd21ffffdfd858d18 0xfdfffffff8187001 0x3fdfffffff818700

def z701 : W := mkw 0x6000002100883900 0x0600000210088390 0xf40484e70198790f 0x7f40484e70198790

def z702 : W := mkw 0x21ffef9d9858d18f 0x521ffef9d9858d18 0xdffb8f1f3878f1cd 0xedffb8f1f3878f1c

def z703 : W := mkw 0x69ffffffed89fd1f 0xe69ffffffed89fd1 0xffffffffff9fff3f 0xfffffffffff9fff3

def z704 : W := mkw 0xc0ffeea03ff6ec0e 0x3c0ffeea03ff6ec0 0x7cfff4e03fff7007 0xc7cfff4e03fff700

def z705 : W := mkw 0x00200e800800c402 0x000200e800800c40 0x03000b0000008600 0x003000b000000860

def z706 : W := mkw 0x41ffefbcad80ec0f 0x641ffefbcad80ec0 0xbfff0ff83f80fe0b 0xdbfff0ff83f80fe0

def z707 : W := mkw 0x80d6a00035520004 0x380d6a0003552000 0x10e4b000399f0007 0x410e4b000399f000

def z708 : W := mkw 0x20628c151858d180 0x120628c151858d18 0xd4e3841f387871cd 0x6d4e3841f387871c

def z709 : W := mkw 0x019d73cac000000f 0xc019d73cac000000 0x311cf7e7c0000000 0x1311cf7e7c000000

def z710 : W := mkw 0xe800002127af3910 0x2e800002127af391 0x00000000079f793f 0x400000000079f793

def z711 : W := mkw 0x68628c3518d9f990 0x168628c3518d9f99 0x0ae3081839fff9ff 0xc0ae3081839fff9f

def z712 : W := mkw 0x00629c565850c080 0x900629c565850c08 0xfee7fcfff86080c0 0xbfee7fcfff86080c

def z713 : W := mkw 0x20628c151858d180 0x120628c151858d18 0xd2e38c1f3878f1cd 0x2d2e38c1f3878f1c

def z714 : W := mkw 0x016bffdec000000f 0xc016bffdec000000 0x4003f4ffc0000000 0x24003f4ffc000000

def z715 : W := mkw 0x6800106340893910 0x8680010634089391 0xff1fffffc7ffffff 0xfff1fffffc7fffff

def z716 : W := mkw 0x68201ef74889fd92 0x868201ef74889fd9 0x83000fffc000fff8 0x383000fffc000fff

def z717 : W := mkw 0x11dff3dec224026f 0xc11dff3dec224026 0x611ff3ffc6640ff6 0x3611ff3ffc6640ff

def z718 : W := mkw 0x6800002118d9f990 0x16800002118d9f99 0x00000000399b7001 0x000000000399b700

def z719 : W := mkw 0x81ffffdef552000f 0xf81ffffdef552000 0xfdfffffff99f0007 0x7fdfffffff99f000

def z720 : W := mkw 0x11ffffdec224026f 0xc11ffffdec224026 0xfdffffffc6640ff6 0x3fdffffffc6640ff

def z721 : W := mkw 0x01f6bfdec0000007 0xc01f6bfdec000000 0xf5e4ffffc0000000 0x3f5e4ffffc000000

def z722 : W := mkw 0x90dfe108b776026d 0x390dfe108b776026 0xfffffb183fff87cf 0xefffffb183fff87c

def z723 : W := mkw 0x01201fdec0000003 0xc01201fdec000000 0xcf030fffc06081cc 0xfcf030fffc06081c

def z724 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0xfcfff0003fff080f 0xdfcfff0003fff080

def z725 : W := mkw 0x010013dec0000003 0xc010013dec000000 0x010003ffc0000000 0x3010003ffc000000

def z726 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0x3ffc0fe03f80f603 0xc3ffc0fe03f80f60

def z727 : W := mkw 0xc06beea01af6ec0e 0x1c06beea01af6ec0 0xc303ffe0007ffe0c 0x1c303ffe0007ffe0

def z728 : W := mkw 0x01d6b2d640000006 0xc01d6b2d64000000 0x0004b0e700000000 0x00004b0e70000000

def z729 : W := mkw 0x019d73cac000000f 0xc019d73cac000000 0x611cf3e7c0000000 0x3611cf3e7c000000

def z730 : W := mkw 0x01201ed640000002 0xc01201ed64000000 0x800004e7c0000000 0x3800004e7c000000

def z731 : W := mkw 0x0094000025000000 0x2009400002500000 0x74e4f000399f0007 0x474e4f000399f000

def z732 : W := mkw 0x81fffed65276000e 0xd81fffed65276000 0x50e7f4e7007f0004 0x050e7f4e7007f000

def z733 : W := mkw 0x01629fded0500003 0xd01629fded050000 0xdde38ffff8780005 0xfdde38ffff878000

def z734 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0x0bf80fe03e00f600 0x80bf80fe03e00f60

def z735 : W := mkw 0x01bd5fdec000000b 0xc01bd5fdec000000 0xfdff4fffc0000000 0x3fdff4fffc000000

def z736 : W := mkw 0x0042800010500000 0x1004280001050000 0xfee7f818f9ff89ff 0xffee7f818f9ff89f

def z737 : W := mkw 0x90dfe0003776026c 0x390dfe0003776026 0x7cfff0003fff01f7 0xc7cfff0003fff01f

def z738 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0x7cfff0003ffb0001 0x87cfff0003ffb000

def z739 : W := mkw 0x816bffded276000f 0xd816bffded276000 0xc103ffffc07f0004 0x3c103ffffc07f000

def z740 : W := mkw 0x0162bed640000006 0xc0162bed64000000 0x0000b4e700000000 0x00000b4e70000000

def z741 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0xfefff8003fff800f 0xcfefff8003fff800

def z742 : W := mkw 0x6800002100893910 0x0680000210089391 0x02000000079fff3f 0xc02000000079fff3

def z743 : W := mkw 0x01ffffdec224000f 0xc01ffffdec224000 0xfdffffffc7ff0007 0xffdffffffc7ff000

def z744 : W := mkw 0x48b40ea02d81ec12 0x248b40ea02d81ec1 0xbffc0fe03f87fe3b 0xdbffc0fe03f87fe3

def z745 : W := mkw 0x414bf17eed80ec0d 0xe414bf17eed80ec0 0x4203f01fff80fe0b 0xe4203f01fff80fe0

def z746 : W := mkw 0x0000104240000000 0x8000010424000000 0xf404f4e7c1870002 0x3f404f4e7c187000

def z747 : W := mkw 0x00628c1400000000 0x000628c140000000 0xfce78cff00000000 0x3fce78cff0000000

def z748 : W := mkw 0x01f6bed66d00c406 0xe01f6bed66d00c40 0x10e4b4e738000000 0x010e4b4e73800000

def z749 : W := mkw 0x68201c774889f990 0x868201c774889f99 0x800004e7c0007938 0x3800004e7c000793

def z750 : W := mkw 0x48629c7658d1e890 0x948629c7658d1e89 0x2ae778f8f9e788f2 0x92ae778f8f9e788f

def z751 : W := mkw 0x11ffffdec224026f 0xc11ffffdec224026 0xffffffffc66087cc 0xfffffffffc66087c

def z752 : W := mkw 0x6809412980893919 0x0680941298089391 0xed1b4b18c19f793f 0x7ed1b4b18c19f793

def z753 : W := mkw 0x80dfe108b776000d 0x380dfe108b776000 0xfdfffb18ffff093f 0xffdfffb18ffff093

def z754 : W := mkw 0x7809412982ad3b79 0x07809412982ad3b7 0x40034018c1ff79ff 0x640034018c1ff79f

def z755 : W := mkw 0x01f69fdec0000003 0xc01f69fdec000000 0xfdff8fffc0000000 0x3fdff8fffc000000

def z756 : W := mkw 0x11629fdec0000263 0xc11629fdec000026 0xdfe38fffc0608ffc 0xfdfe38fffc0608ff

def z757 : W := mkw 0x00d6b04240000004 0x800d6b0424000000 0x10e4b4e700000000 0x010e4b4e70000000

def z758 : W := mkw 0x90dfe0003776026c 0x390dfe0003776026 0xfefff000ffff8fff 0xffefff000ffff8ff

def z759 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0x7efff8183fff80c7 0xc7efff8183fff80c

def z760 : W := mkw 0x81ffffdef776000f 0xf81ffffdef776000 0x7cfff4ffffff0007 0xe7cfff4ffffff000

def z761 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0x09fb0fff00000000 0x009fb0fff0000000

def z762 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0x7cfff0003fff093f 0xc7cfff0003fff093

def z763 : W := mkw 0x6894002125893910 0x2689400212589391 0x3cfc00003f9f793f 0xc3cfc00003f9f793

def z764 : W := mkw 0x01201fdec0000003 0xc01201fdec000000 0xad180fffc0000000 0x3ad180fffc000000

def z765 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0x50e7f0003fff0007 0xc50e7f0003fff000

def z766 : W := mkw 0x00628c141850c080 0x100628c141850c08 0xdee38c1f3860f0c9 0xedee38c1f3860f0c

def z767 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xfdffffffc06001c4 0x3fdffffffc06001c

def z768 : W := mkw 0xe8dfe0213ffffd1c 0x3e8dfe0213ffffd1 0x7efff0003fffff3f 0xc7efff0003fffff3

def z769 : W := mkw 0x81ffffdef776000f 0xf81ffffdef776000 0xfdfffffffffb0001 0xbfdfffffffffb000

def z770 : W := mkw 0x01f6bed65850c086 0xd01f6bed65850c08 0x10e4b4e738000000 0x010e4b4e73800000

def z771 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0xfcfff4073fff0007 0xefcfff4073fff000

def z772 : W := mkw 0x804bf0425276000c 0x9804bf0425276000 0xf407f4e7c07f0004 0x3f407f4e7c07f000

def z773 : W := mkw 0x81ffffdee726000f 0xe81ffffdee726000 0xfdffffffc7e70006 0xffdffffffc7e7000

def z774 : W := mkw 0x0042800010500000 0x1004280001050000 0x5ce7b00039fb0005 0xc5ce7b00039fb000

def z775 : W := mkw 0x81ffffdeff76c08f 0xf81ffffdeff76c08 0xffffffffffff80c7 0xfffffffffffff80c

def z776 : W := mkw 0xe0dfe0213ffefd8c 0x3e0dfe0213ffefd8 0x7efff0003fffffcf 0xc7efff0003fffffc

def z777 : W := mkw 0x81ffffdee726000f 0xe81ffffdee726000 0xfdffffffc6000000 0x3fdffffffc600000

def z778 : W := mkw 0x80d6a00035520004 0x380d6a0003552000 0x10e4b0003f9b0003 0xc10e4b0003f9b000

def z779 : W := mkw 0x01ffffded274000f 0xd01ffffded274000 0xfdfffffffe7c0007 0xffdfffffffe7c000

def z780 : W := mkw 0x00dff0424000000c 0x800dff0424000000 0x7cfff4e700000000 0x07cfff4e70000000

def z781 : W := mkw 0xa0bd6c152f2ed18c 0x2a0bd6c152f2ed18 0xa21c7c1f0787f1ca 0x2a21c7c1f0787f1c

def z782 : W := mkw 0x01ffffdeed00c00f 0xe01ffffdeed00c00 0xffffffffff80f00b 0xfffffffffff80f00

def z783 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0x11fcb7e700000000 0x011fcb7e70000000

def z784 : W := mkw 0x11f6bed642240266 0xc11f6bed64224026 0x12e4b4e706648ffe 0xc12e4b4e706648ff

def z785 : W := mkw 0x81ffffdef552000f 0xf81ffffdef552000 0xfdffffffff9b0003 0xffdffffffff9b000

def z786 : W := mkw 0x019d73dec000000f 0xc019d73dec000000 0x211c73ffc0000000 0x3211c73ffc000000

def z787 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0xfcfff0003fff010f 0xefcfff0003fff010

def z788 : W := mkw 0x01f6bed640000006 0xc01f6bed64000000 0xbffcbfe706008e0a 0xdbffcbfe706008e0

def z789 : W := mkw 0x11b41fdec0000263 0xc11b41fdec000026 0xbffc0fffc6008ffa 0xfbffc0fffc6008ff

def z790 : W := mkw 0x1009410882240269 0x0100941088224026 0xef1b4b18c7ff8fff 0xfef1b4b18c7ff8ff

def z791 : W := mkw 0x11ffffdec000026f 0xc11ffffdec000026 0xfdffffffc00001f0 0x3fdffffffc00001f

def z792 : W := mkw 0x60d682b535d83d82 0x360d682b535d83d8 0x611f83ff07f80fc6 0x3611f83ff07f80fc

def z793 : W := mkw 0x600000212d88fd00 0x2600000212d88fd0 0x020000003f98ff0f 0xc020000003f98ff0

def z794 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xddfb8fffc0000000 0x3ddfb8fffc000000

def z795 : W := mkw 0x90dff14af776026d 0xb90dff14af776026 0xffffffffffff8fff 0xfffffffffffff8ff

def z796 : W := mkw 0x01201fdec0000003 0xc01201fdec000000 0xe5004fffc004093e 0x7e5004fffc004093

def z797 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0x74e7f00039ff0007 0x474e7f00039ff000

def z798 : W := mkw 0x00b40e8000000002 0x000b40e800000000 0xfdfc8fe700000000 0x3fdfc8fe70000000

def z799 : W := mkw 0x01f6bed640000006 0xc01f6bed64000000 0xb4e4b4e700000000 0x1b4e4b4e70000000

def z800 : W := mkw 0x0000000000000000 0x0000000000000000 0xf40484e700000000 0x3f40484e70000000

def z801 : W := mkw 0x01ffffdee500000f 0xe01ffffdee500000 0xfdffffffff9f0007 0xffdffffffff9f000

def z802 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0x18ffb0003fff0007 0xc18ffb0003fff000

def z803 : W := mkw 0xe800002135db3910 0x3e800002135db391 0x00000000399b7001 0x000000000399b700

def z804 : W := mkw 0x204280151858d180 0x1204280151858d18 0x5ee3801f3878f1cd 0xe5ee3801f3878f1c

def z805 : W := mkw 0x11ffffdec224026f 0xc11ffffdec224026 0x1bffbfff066086c0 0x81bffbfff066086c

def z806 : W := mkw 0x80d6a00037760004 0x380d6a0003776000 0x10e4b00039ff0005 0x010e4b00039ff000

def z807 : W := mkw 0x00201c5640000000 0x800201c564000000 0x80000cffc0000000 0x380000cffc000000

def z808 : W := mkw 0x0000000000000000 0x0000000000000000 0xef1b4b18c6648ffe 0xfef1b4b18c6648ff

def z809 : W := mkw 0x80d6a00035520004 0x380d6a0003552000 0x34e4b000399b0003 0x434e4b000399b000

def z810 : W := mkw 0x01629fded850c083 0xd01629fded850c08 0x8be30ffff86080c0 0xb8be30ffff86080c

def z811 : W := mkw 0x81ffffdef776000f 0xf81ffffdef776000 0xfdfffffff9ff0005 0x3fdfffffff9ff000

def z812 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xedfb4fffc0000000 0x3edfb4fffc000000

def z813 : W := mkw 0x00d6b04240000004 0x800d6b0424000000 0xf4e4f4e7c0000000 0x3f4e4f4e7c000000

def z814 : W := mkw 0x81ffffdef776000f 0xf81ffffdef776000 0xffffffffffff81cf 0xfffffffffffff81c

def z815 : W := mkw 0x680000212d89fd10 0x2680000212d89fd1 0x00000000399b7001 0x000000000399b700

def z816 : W := mkw 0x20628c151858d180 0x120628c151858d18 0xfee7fc1f3878f1cd 0xefee7fc1f3878f1c

def z817 : W := mkw 0x7809516bc2ad3b79 0x87809516bc2ad3b7 0x1b1fbfff07fbf6c1 0x81b1fbfff07fbf6c

def z818 : W := mkw 0x11ffffdec224026f 0xc11ffffdec224026 0x8bfb0fffc6608ff8 0xb8bfb0fffc6608ff

def z819 : W := mkw 0x0000104240000000 0x8000010424000000 0xfc07fcffc0000000 0x3fc07fcffc000000

def z820 : W := mkw 0x68201ee34889fd12 0x868201ee34889fd1 0x800004e7c0007938 0x3800004e7c000793

def z821 : W := mkw 0x20628c151858d180 0x120628c151858d18 0x9ae38c1f3878f1c9 0xa9ae38c1f3878f1c

def z822 : W := mkw 0x01b41fdec0000003 0xc01b41fdec000000 0x89f80fffc0000000 0x389f80fffc000000

def z823 : W := mkw 0x1009410882240269 0x0100941088224026 0xff1f4ff8c6648ffe 0xfff1f4ff8c6648ff

def z824 : W := mkw 0x0000104240000000 0x8000010424000000 0x000004e700000000 0x0000004e70000000

def z825 : W := mkw 0x01295fdec000000b 0xc01295fdec000000 0x891b0fffc0000000 0x3891b0fffc000000

def z826 : W := mkw 0x01201fdec0000003 0xc01201fdec000000 0x9104bfffc0000000 0x39104bfffc000000

def z827 : W := mkw 0x90d6a108b5520265 0x390d6a108b552026 0x93e4bb18f99b8ff9 0x393e4bb18f99b8ff

def z828 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0xffff4ff8ffe4ffff 0xfffff4ff8ffe4fff

def z829 : W := mkw 0x90dfe108b776026d 0x390dfe108b776026 0xfffffb183fff8ecf 0xdfffffb183fff8ec

def z830 : W := mkw 0x80dfe108b776000d 0x380dfe108b776000 0xfffffb18ffff81cf 0xffffffb18ffff81c

def z831 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xf5fcf7e7c0000000 0x3f5fcf7e7c000000

def z832 : W := mkw 0x1009514ac2240269 0x81009514ac224026 0xff1fffffc66086c0 0xbff1fffffc66086c

def z833 : W := mkw 0x00b40e802d00c402 0x200b40e802d00c40 0xbffc0fe03e00f609 0xdbffc0fe03e00f60

def z834 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xfdffffffc000080a 0x7fdffffffc000080

def z835 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0xfcfff000ffff0007 0xffcfff000ffff000

def z836 : W := mkw 0x80dfe0143776008c 0x380dfe0143776008 0x7cfff0183fff00c7 0xc7cfff0183fff00c

def z837 : W := mkw 0x20628c151858d180 0x120628c151858d18 0x8ae30c1f3878f1cd 0xe8ae30c1f3878f1c

def z838 : W := mkw 0x81dff3def776000f 0xf81dff3def776000 0x7dfff3ffffff0007 0xf7dfff3ffffff000

def z839 : W := mkw 0x01f6bfdec0000007 0xc01f6bfdec000000 0xdde7bfffc0000000 0x3dde7bfffc000000

def z840 : W := mkw 0x01295fdec000000b 0xc01295fdec000000 0xfd1fffffc0000000 0x3fd1fffffc000000

def z841 : W := mkw 0x01ffffdee500000f 0xe01ffffdee500000 0xfdffffffc7800002 0x3fdffffffc780000

def z842 : W := mkw 0x01201fdec0000003 0xc01201fdec000000 0xa1047fffc0000000 0x3a1047fffc000000

def z843 : W := mkw 0x00b41ec240000002 0x800b41ec24000000 0xbdfc0fe7c0000000 0x3bdfc0fe7c000000

def z844 : W := mkw 0x01ffffdec800c40f 0xc01ffffdec800c40 0xffffffffc0008600 0x3ffffffffc000860

def z845 : W := mkw 0x519d73eae7a42e6f 0xe519d73eae7a42e6 0x211c73e0c7840e32 0x1211c73e0c7840e3

def z846 : W := mkw 0x81201fdef7760003 0xf81201fdef776000 0x81000fffffff0007 0xf81000fffffff000

def z847 : W := mkw 0x0000104240000000 0x8000010424000000 0xf404f4e7c000010c 0x7f404f4e7c000010

def z848 : W := mkw 0x78201d7fc889fbf1 0x878201d7fc889fbf 0x83000fffc000fff8 0x383000fffc000fff

def z849 : W := mkw 0x104bc10892740269 0x1104bc1089274026 0xfffffb18ffff8fff 0xffffffb18ffff8ff

def z850 : W := mkw 0x60d680213dd8fd80 0x360d680213dd8fd8 0x7eff80003ff8ffcf 0xc7eff80003ff8ffc

def z851 : W := mkw 0x80dfe0003552000c 0x380dfe0003552000 0x50e7f000399b0001 0x050e7f000399b000

def z852 : W := mkw 0x91ffffdef776026f 0xf91ffffdef776026 0xfdffffffffff01f7 0xffdffffffffff01f

def z853 : W := mkw 0x01ffffded050000f 0xd01ffffded050000 0xfdfffffff8600000 0xbfdfffffff860000

def z854 : W := mkw 0x80d6a00037760004 0x380d6a0003776000 0x10e4b0003ffb0001 0x810e4b0003ffb000

def z855 : W := mkw 0x819d73cae726000f 0xe819d73cae726000 0xf51cf7e7c79f0007 0x7f51cf7e7c79f000

def z856 : W := mkw 0x6800002125893d10 0x26800002125893d1 0x00000000079f7f3f 0x400000000079f7f3

def z857 : W := mkw 0x00f68e9400000002 0x000f68e940000000 0xffff8fff06608fce 0xfffff8fff06608fc

def z858 : W := mkw 0x81ffffdee502000f 0xe81ffffdee502000 0xfdffffffc1830000 0x3fdffffffc183000

def z859 : W := mkw 0x20628c151858d180 0x120628c151858d18 0x0ae30c1f3860f0c0 0x80ae30c1f3860f0c

def z860 : W := mkw 0x68f69ef77dd9fd92 0xb68f69ef77dd9fd9 0x10e4b4e7399b7001 0x010e4b4e7399b700

def z861 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xbdfcffe7c0000000 0x1bdfcffe7c000000

def z862 : W := mkw 0x0000104240000000 0x8000010424000000 0xf404f4e7c0040832 0x3f404f4e7c004083

def z863 : W := mkw 0x91ffffded276026f 0xd91ffffded276026 0xfdffffffc07f01f4 0x3fdffffffc07f01f

def z864 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xffffffffc0008e08 0x3ffffffffc0008e0

def z865 : W := mkw 0x8000104277760000 0xb800010427776000 0xf404f4e7ffff0007 0xff404f4e7ffff000

def z866 : W := mkw 0x01295fdec224000b 0xc01295fdec224000 0xed1b4fffc6640006 0xfed1b4fffc664000

def z867 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xd1e7ffffc0000000 0x3d1e7ffffc000000

def z868 : W := mkw 0x80dff14af776000d 0xb80dff14af776000 0xfdffffffffff0007 0xffdffffffffff000

def z869 : W := mkw 0x0000104240000000 0x8000010424000000 0xe40044e7c004093e 0x7e40044e7c004093

def z870 : W := mkw 0x6800002100893910 0x0680000210089391 0xc4000000019f793f 0x6c4000000019f793

def z871 : W := mkw 0x01201ed640000002 0xc01201ed64000000 0x80000cff00000000 0x280000cff0000000

def z872 : W := mkw 0x6800002100893910 0x0680000210089391 0x20047000019f793f 0x420047000019f793

def z873 : W := mkw 0x00629c5640000000 0x800629c564000000 0xdce7bcff00000000 0x2dce7bcff0000000

def z874 : W := mkw 0x81dff15ef776000d 0xf81dff15ef776000 0xfcfff4ffffff0007 0xffcfff4ffffff000

def z875 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0xbffc0fe03f84ff3f 0xdbffc0fe03f84ff3

def z876 : W := mkw 0x20628c151858d180 0x120628c151858d18 0xfee78c1f39f8f1cf 0xefee78c1f39f8f1c

def z877 : W := mkw 0x00b41ec265000002 0xa00b41ec26500000 0xfdfcffe7ff9f0007 0xffdfcffe7ff9f000

def z878 : W := mkw 0xb84bf14bd27f137d 0x9b84bf14bd27f137 0x4003f01fc07f01f4 0x24003f01fc07f01f

def z879 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0x68fff0003fff0006 0x868fff0003fff000

def z880 : W := mkw 0x0000104240000000 0x8000010424000000 0x5004f4e7c0000000 0x25004f4e7c000000

def z881 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0x3dfc07e03f807e03 0xd3dfc07e03f807e0

def z882 : W := mkw 0x589d53eae7a52e7b 0xa589d53eae7a52e7 0x211c73e0c7870e32 0x1211c73e0c7870e3

def z883 : W := mkw 0x6800002100893910 0x0680000210089391 0x40004000c19f793f 0x640004000c19f793

def z884 : W := mkw 0x80dfe0003552000c 0x380dfe0003552000 0x18ffb000399b0001 0x018ffb000399b000

def z885 : W := mkw 0x00dfe0002500000c 0x200dfe0002500000 0x7cfff0003f9f0007 0xc7cfff0003f9f000

def z886 : W := mkw 0x80dfe108b552000d 0x380dfe108b552000 0xfdfffb18f99b0001 0x3fdfffb18f99b000

def z887 : W := mkw 0x11201fdec0000263 0xc11201fdec000026 0x81000fffc00001f0 0x381000fffc00001f

def z888 : W := mkw 0xd89d716ae7a72a7d 0xad89d716ae7a72a7 0x211c73e0c7870e32 0x1211c73e0c7870e3

def z889 : W := mkw 0x409402a02d80ec02 0x2409402a02d80ec0 0x3ffc03e03f80fe0b 0xd3ffc03e03f80fe0

def z890 : W := mkw 0x0000104240000000 0x8000010424000000 0x9004b4e7c0000000 0x39004b4e7c000000

def z891 : W := mkw 0x11ffffdec224026f 0xc11ffffdec224026 0xfdffffffc0040030 0x3fdffffffc004003

def z892 : W := mkw 0x81f6bed650520006 0xd81f6bed65052000 0x10e4b4e7001b0000 0x010e4b4e7001b000

def z893 : W := mkw 0x6800002110d93910 0x16800002110d9391 0x0000000039ff793f 0xc0000000039ff793

def z894 : W := mkw 0x01b43ed640000006 0xc01b43ed64000000 0x000434e700000000 0x0000434e70000000

def z895 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0xfffffb00ffff8f3f 0xffffffb00ffff8f3

def z896 : W := mkw 0x01ffffded050000f 0xd01ffffded050000 0xfdfffffff8180001 0x3fdfffffff818000

def z897 : W := mkw 0x6800002100893910 0x0680000210089391 0x80000000c19f793f 0x780000000c19f793

def z898 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0xfffcffe03f80fe0b 0xdfffcffe03f80fe0

def z899 : W := mkw 0x78201febc889ff73 0x878201febc889ff7 0x83000fffc000fff8 0x383000fffc000fff

def z900 : W := mkw 0x01fffed64000000e 0xc01fffed64000000 0xfdffffe700000000 0x1fdffffe70000000

def z901 : W := mkw 0x1009410882240269 0x0100941088224026 0xff1bcf1fc6648ffe 0xfff1bcf1fc6648ff

def z902 : W := mkw 0x01629ed640000002 0xc01629ed64000000 0xdce38cff00000000 0x2dce38cff0000000

def z903 : W := mkw 0x7800002102ad3b70 0x07800002102ad3b7 0x020000000664fffe 0xc020000000664fff

def z904 : W := mkw 0x219d73cbd858d18f 0xd219d73cbd858d18 0x231c73e0f878f1cd 0xd231c73e0f878f1c

def z905 : W := mkw 0x0009504240000008 0x8000950424000000 0xfc1ff4e7c0000000 0x3fc1ff4e7c000000

def z906 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0xfffc8fe73f80fe0b 0xffffc8fe73f80fe0

def z907 : W := mkw 0x6800002100893910 0x0680000210089391 0x000000000180793b 0x4000000000180793

def z908 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0x70fff0003fff0007 0x070fff0003fff000

def z909 : W := mkw 0x0000104240000000 0x8000010424000000 0x3004f4e7c0000000 0x13004f4e7c000000

def z910 : W := mkw 0x00f68e9400000002 0x000f68e940000000 0xdce78cff00000000 0x2dce78cff0000000

def z911 : W := mkw 0x804be0001276000c 0x1804be0001276000 0x7ce7f00039ff0007 0xc7ce7f00039ff000

def z912 : W := mkw 0x0000104240000000 0x8000010424000000 0xd404b4e700000000 0x2d404b4e70000000

def z913 : W := mkw 0x81f6bed675520006 0xf81f6bed67552000 0xdce7bcff39fb0005 0xedce7bcff39fb000

def z914 : W := mkw 0xf8dfe02137ff3b7c 0x3f8dfe02137ff3b7 0x7efff0003fffffff 0xc7efff0003ffffff

def z915 : W := mkw 0x809d60002726000c 0x2809d60002726000 0x7cfcf0003f9f0007 0xc7cfcf0003f9f000

def z916 : W := mkw 0x81ffffded276000f 0xd81ffffded276000 0xfdffffffc1ff0007 0x7fdffffffc1ff000

def z917 : W := mkw 0x90dfe108b776026d 0x390dfe108b776026 0xfffffb18ffff86c7 0xffffffb18ffff86c

def z918 : W := mkw 0x6800106340893910 0x8680010634089391 0x7404f4e7c19f7837 0x57404f4e7c19f783

def z919 : W := mkw 0x114bf15ec224026d 0xc114bf15ec224026 0xff1fffffc6648ffe 0xfff1fffffc6648ff

def z920 : W := mkw 0x0000104240000000 0x8000010424000000 0x7404f4e700000000 0x07404f4e70000000

def z921 : W := mkw 0x28b41ec36d09d512 0xa28b41ec36d09d51 0x4bf8fb07fe1f8734 0xa4bf8fb07fe1f873

def z922 : W := mkw 0x0094000025000000 0x2009400002500000 0x10e4b000399b0001 0x010e4b000399b000

def z923 : W := mkw 0x014bf3dec000000f 0xc014bf3dec000000 0x4103f3ffc0000000 0x34103f3ffc000000

def z924 : W := mkw 0x0094104265000000 0xa009410426500000 0xfcfcf4e7ff800003 0xffcfcf4e7ff80000

def z925 : W := mkw 0x01295fdec000000b 0xc01295fdec000000 0xa1184fffc0000000 0x3a1184fffc000000

def z926 : W := mkw 0x01f6bfdec0000007 0xc01f6bfdec000000 0x81e00fffc0000000 0x381e00fffc000000

def z927 : W := mkw 0x01ffffded050000f 0xd01ffffded050000 0xfdfffffff9ff0007 0xffdfffffff9ff000

def z928 : W := mkw 0x91ffffdef776026f 0xf91ffffdef776026 0xfffffffffe648ffe 0xffffffffffe648ff

def z929 : W := mkw 0x80d6b04275520004 0xb80d6b0427552000 0xf4e4f4e7f99b0001 0x3f4e4f4e7f99b000

def z930 : W := mkw 0x20628c151858d180 0x120628c151858d18 0xdfe38f1f3878ffcd 0xfdfe38f1f3878ffc

def z931 : W := mkw 0x11f6bfdec0000267 0xc11f6bfdec000026 0x93e4bfffc0008ff8 0x393e4bfffc0008ff

def z932 : W := mkw 0x11ffffdec224026f 0xc11ffffdec224026 0xffffffffc7ff8fff 0xfffffffffc7ff8ff

def z933 : W := mkw 0x1009410882240269 0x0100941088224026 0x4b1b4b18c6648ffe 0xe4b1b4b18c6648ff

def z934 : W := mkw 0x7809412982ad3b79 0x07809412982ad3b7 0xef1b4b18c664fffe 0xfef1b4b18c664fff

def z935 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0x7dfff7e7c0000000 0x17dfff7e7c000000

def z936 : W := mkw 0x01ffffdeed00c40f 0xe01ffffdeed00c40 0xffffffffff808603 0xfffffffffff80860

def z937 : W := mkw 0x81ffffdef776000f 0xf81ffffdef776000 0x50e7f4fff9ff0005 0x250e7f4fff9ff000

def z938 : W := mkw 0x20628c151858d180 0x120628c151858d18 0xfffb8f1f3878f1cd 0xffffb8f1f3878f1c

def z939 : W := mkw 0x00b41ec240000002 0x800b41ec24000000 0x10e4b4e700000000 0x010e4b4e70000000

def z940 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0x28ff70003fff0007 0xc28ff70003fff000

def z941 : W := mkw 0x680000210889f990 0x0680000210889f99 0x020000000000f9f8 0x0020000000000f9f

def z942 : W := mkw 0x01ffffdec800c00f 0xc01ffffdec800c00 0xfffffffff8008000 0xbfffffffff800800

def z943 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xbdffbfff00000000 0x1bdffbfff0000000

def z944 : W := mkw 0x01fffed64000000e 0xc01fffed64000000 0xfcfffcff00000000 0x2fcfffcff0000000

def z945 : W := mkw 0x016bffdec000000f 0xc016bffdec000000 0xf507ffffc0000000 0x3f507ffffc000000

def z946 : W := mkw 0x6800002100893910 0x0680000210089391 0x64004000019f793f 0x464004000019f793

def z947 : W := mkw 0x80d6a00035520004 0x380d6a0003552000 0x7cffb0003ffb0007 0xc7cffb0003ffb000

def z948 : W := mkw 0x50bd4fa8afa4ee6b 0x250bd4fa8afa4ee6 0x50e744f8f9e471f5 0x250e744f8f9e471f

def z949 : W := mkw 0x01ffffdee500000f 0xe01ffffdee500000 0xffffffffff808e0b 0xfffffffffff808e0

def z950 : W := mkw 0x01bd7fdec000000f 0xc01bd7fdec000000 0x81180fffc0000000 0x381180fffc000000

def z951 : W := mkw 0x81ffffdef776000f 0xf81ffffdef776000 0x19ffbfff3ffb0001 0x819ffbfff3ffb000

def z952 : W := mkw 0x6800106340893910 0x8680010634089391 0xf404f4e7c19f7135 0x3f404f4e7c19f713

def z953 : W := mkw 0x20628c151858d180 0x120628c151858d18 0x1ae38c1f3878f1cd 0xc1ae38c1f3878f1c

def z954 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xffffffffc00081c8 0x3ffffffffc00081c

def z955 : W := mkw 0x600000213dd8fd80 0x3600000213dd8fd8 0x020000003f98fe0b 0xc020000003f98fe0

def z956 : W := mkw 0x6800002100893910 0x0680000210089391 0xa4000000019f793f 0x5a4000000019f793

def z957 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xfdffffffc0180005 0x7fdffffffc018000

def z958 : W := mkw 0x6000002118d8f980 0x16000002118d8f98 0x0200000039f8f9cf 0xc0200000039f8f9c

def z959 : W := mkw 0x11ffffdec224026f 0xc11ffffdec224026 0xfdffffffc06409fe 0x7fdffffffc06409f

def z960 : W := mkw 0x81fffed67776000e 0xf81fffed67776000 0xfdffffe73fff0007 0xdfdffffe73fff000

def z961 : W := mkw 0x01201fdec0000003 0xc01201fdec000000 0x81000fffc0000938 0x381000fffc000093

def z962 : W := mkw 0x00b40e9400000002 0x000b40e940000000 0xbdfc0fff00000000 0x3bdfc0fff0000000

def z963 : W := mkw 0x6842802110d93910 0x16842802110d9391 0x5ce3800039ff793f 0xc5ce3800039ff793

def z964 : W := mkw 0x80d6a00035520004 0x380d6a0003552000 0xf4e4f000f99f093f 0x7f4e4f000f99f093

def z965 : W := mkw 0x11ffffdec224026f 0xc11ffffdec224026 0xffffffffc6648ef2 0xbffffffffc6648ef

def z966 : W := mkw 0x20628c151858d180 0x120628c151858d18 0x52e3841f3878f1cd 0xe52e3841f3878f1c

def z967 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0x7cfff4ffc0000000 0x27cfff4ffc000000

def z968 : W := mkw 0xe8dff06377ff391c 0xbe8dff06377ff391 0x88fb04e7fe607938 0xb88fb04e7fe60793

def z969 : W := mkw 0xe8dfe02137ff391c 0x3e8dfe02137ff391 0x7cfff0003fff7007 0xc7cfff0003fff700

def z970 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0xfcfff4e03fff0007 0xdfcfff4e03fff000

def z971 : W := mkw 0x6800106340893910 0x8680010634089391 0xfc07fcffc19f793f 0x7fc07fcffc19f793

def z972 : W := mkw 0x1000114ac0000261 0x81000114ac000026 0xf704ffffc0008ff8 0x3f704ffffc0008ff

def z973 : W := mkw 0x6800002100893910 0x0680000210089391 0x00000000019f0936 0x000000000019f093

def z974 : W := mkw 0x80d6a00035520004 0x380d6a0003552000 0x7ce7f00039ff0007 0xc7ce7f00039ff000

def z975 : W := mkw 0x81ffffdef552000f 0xf81ffffdef552000 0xfdfffffff9fb0005 0xffdfffffff9fb000

def z976 : W := mkw 0x20628c151858d180 0x120628c151858d18 0xfee3cc1f387cf1cf 0xefee3cc1f387cf1c

def z977 : W := mkw 0x20628c151858d180 0x120628c151858d18 0xfee7fc1ff9fff9ff 0xffee7fc1ff9fff9f

def z978 : W := mkw 0x0000104240000000 0x8000010424000000 0xf404f4e7c0000938 0x3f404f4e7c000093

def z979 : W := mkw 0x00f68e943d50c482 0x300f68e943d50c48 0xffff8fff3e6086c0 0xbffff8fff3e6086c

def z980 : W := mkw 0x11295fdec224026b 0xc11295fdec224026 0xa1184fffc6040e32 0x3a1184fffc6040e3

def z981 : W := mkw 0x80d6a00035520004 0x380d6a0003552000 0xbffcbb003f9b8e0b 0xdbffcbb003f9b8e0

def z982 : W := mkw 0x11ffffdeda74c2ef 0xd11ffffdeda74c2e 0xfffffffffe6086c0 0xbfffffffffe6086c

def z983 : W := mkw 0x20628e951858d582 0x120628e951858d58 0xdfe38f1f3878f7cd 0xedfe38f1f3878f7c

def z984 : W := mkw 0x11ffffdee724026f 0xe11ffffdee724026 0xffffffffffe48fff 0xfffffffffffe48ff

def z985 : W := mkw 0x0000104240000000 0x8000010424000000 0x7404f4e7019f0007 0x47404f4e7019f000

def z986 : W := mkw 0x81ffffdef776000f 0xf81ffffdef776000 0xfdfffffffe640006 0xffdfffffffe64000

def z987 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xc9fbffffc0000000 0x3c9fbffffc000000

def z988 : W := mkw 0x014bf15ec000000d 0xc014bf15ec000000 0xc003f4ffc0000000 0x3c003f4ffc000000

def z989 : W := mkw 0x11ffffded274026f 0xd11ffffded274026 0xfffffffffe7c8fff 0xffffffffffe7c8ff

def z990 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0x2bfc0be03f80fe0b 0xd2bfc0be03f80fe0

def z991 : W := mkw 0x90dfe108b776026d 0x390dfe108b776026 0x7cfff0183fff00c7 0xc7cfff0183fff00c

def z992 : W := mkw 0x01ffffdec224000f 0xc01ffffdec224000 0xfdffffffc0640004 0x3fdffffffc064000

def z993 : W := mkw 0xf800002137ff3b70 0x3f800002137ff3b7 0x020000003fffffff 0xc020000003ffffff

def z994 : W := mkw 0x81ffffdef776000f 0xf81ffffdef776000 0xfdffffffc7ff0006 0x3fdffffffc7ff000

def z995 : W := mkw 0x01297fdec000000f 0xc01297fdec000000 0x81007fffc0000000 0x381007fffc000000

def z996 : W := mkw 0x016bffdec000000f 0xc016bffdec000000 0x81030fffc0000000 0x381030fffc000000

def z997 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0x1bfc0fe03f80fe0b 0xc1bfc0fe03f80fe0

def z998 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0x7cfff0003f9f0003 0x07cfff0003f9f000

def z999 : W := mkw 0x0000104240000000 0x8000010424000000 0xfd1cffe7c0000000 0x3fd1cffe7c000000

def z1000 : W := mkw 0x680000210889fd10 0x0680000210889fd1 0x02000000019fff3f 0x402000000019fff3

def z1001 : W := mkw 0x7809412982ad3b79 0x07809412982ad3b7 0xff1ffb18c7ffffff 0xfff1ffb18c7fffff

def z1002 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0xfcfff4003fff700f 0xcfcfff4003fff700

def z1003 : W := mkw 0x1000104242240260 0x8100010424224026 0xf604f4e7c6648ffe 0xff604f4e7c6648ff

def z1004 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xfdffffffc19b0001 0x3fdffffffc19b000

def z1005 : W := mkw 0x91ffffdee726026f 0xe91ffffdee726026 0xfdffffffc7870e32 0x3fdffffffc7870e3

def z1006 : W := mkw 0x6800002118d9f990 0x16800002118d9f99 0x020000003878f9fd 0xc020000003878f9f

def z1007 : W := mkw 0x6800002100893910 0x0680000210089391 0x34040000019f793f 0x434040000019f793

def z1008 : W := mkw 0x69ffefbd8089391f 0x469ffefbd8089391 0x09fb0b18019f793f 0x409fb0b18019f793

def z1009 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0x3cffb0003ffb0003 0xc3cffb0003ffb000

def z1010 : W := mkw 0x68201ee34889fd12 0x868201ee34889fd1 0x83000fe70000fe08 0x183000fe70000fe0

def z1011 : W := mkw 0x81ffffdee726000f 0xe81ffffdee726000 0xfdffffffff870003 0xffdffffffff87000

def z1012 : W := mkw 0x01bd7fdec000000f 0xc01bd7fdec000000 0x211c77e7c0000000 0x1211c77e7c000000

def z1013 : W := mkw 0x01201fdec800c003 0xc01201fdec800c00 0x83000fffc000f008 0x383000fffc000f00

def z1014 : W := mkw 0x004bf0424000000c 0x8004bf0424000000 0xf407f4e7c0000000 0x3f407f4e7c000000

def z1015 : W := mkw 0x00628c140800c000 0x000628c140800c00 0xdee38c1f3860f1cd 0xedee38c1f3860f1c

def z1016 : W := mkw 0x6800106340893910 0x8680010634089391 0x7004f4e7c19f7937 0x37004f4e7c19f793

def z1017 : W := mkw 0x01ffffdec800c00f 0xc01ffffdec800c00 0xfdfffffff8007001 0x3fdfffffff800700

def z1018 : W := mkw 0x01f6bed640000006 0xc01f6bed64000000 0x91e4bfe700000000 0x191e4bfe70000000

def z1019 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0xbffc0fe03f9ffe0f 0xdbffc0fe03f9ffe0

def z1020 : W := mkw 0x1009410882240269 0x0100941088224026 0xcb1b4b18c6648ffc 0xbcb1b4b18c6648ff

def z1021 : W := mkw 0x01f6bed640000006 0xc01f6bed64000000 0x00e004e700000000 0x000e004e70000000

def z1022 : W := mkw 0x804be0003776000c 0x3804be0003776000 0x5ce3f0003fff0007 0xc5ce3f0003fff000

def z1023 : W := mkw 0x01dff3dec000000f 0xc01dff3dec000000 0xf51ff7ffc0000000 0x3f51ff7ffc000000

def z1024 : W := mkw 0x01f6bed665000006 0xe01f6bed66500000 0x10e4b4e739800001 0x010e4b4e73980000

def z1025 : W := mkw 0x80d6a00035520004 0x380d6a0003552000 0x74e4f000399b0001 0x074e4f000399b000

def z1026 : W := mkw 0xe8d6a02135db3914 0x3e8d6a02135db391 0x10e4b000399f793f 0x410e4b000399f793

def z1027 : W := mkw 0x306bcd1d9a7cd3e9 0x1306bcd1d9a7cd3e 0x31f8c707fe1c7e33 0x131f8c707fe1c7e3

def z1028 : W := mkw 0xc0b42ea02d82ec06 0x2c0b42ea02d82ec0 0xbffc3fe03f83fe0b 0xdbffc3fe03f83fe0

def z1029 : W := mkw 0x6800002110d93990 0x16800002110d9399 0x0000000001ff79ff 0x40000000001ff79f

def z1030 : W := mkw 0x20628c151858d180 0x120628c151858d18 0xdee38c1f387cf9ff 0xedee38c1f387cf9f

def z1031 : W := mkw 0x68201c774889f990 0x868201c774889f99 0xee034cffc064f9fe 0xfee034cffc064f9f

def z1032 : W := mkw 0x809d70426726000c 0xa809d70426726000 0xf41cf4e7c7870002 0x3f41cf4e7c787000

def z1033 : W := mkw 0x7800012980893b71 0x07800012980893b7 0x83000b18c19fffff 0x783000b18c19ffff

def z1034 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0x48fbf0003fff0007 0xc48fbf0003fff000

def z1035 : W := mkw 0x6800002100893910 0x0680000210089391 0x00000000019f7833 0x000000000019f783

def z1036 : W := mkw 0xe800002135db3910 0x3e800002135db391 0x00000000399f793f 0x400000000399f793

def z1037 : W := mkw 0x20628c151858d180 0x120628c151858d18 0xdee3cc1ff87cf1fd 0xedee3cc1ff87cf1f

def z1038 : W := mkw 0x01201fdec0000003 0xc01201fdec000000 0x01000fff00000000 0x001000fff0000000

def z1039 : W := mkw 0x6800002102ad3910 0x06800002102ad391 0x0000000007ff793f 0xc0000000007ff793

def z1040 : W := mkw 0x68201ee34889fd12 0x868201ee34889fd1 0xef184fe7c604ff3e 0xfef184fe7c604ff3

def z1041 : W := mkw 0xf8dfe129b7ff3b7d 0x3f8dfe129b7ff3b7 0xfffffb18ffffffff 0xffffffb18fffffff

def z1042 : W := mkw 0x69201fffc889fd13 0xc69201fffc889fd1 0x83000fffc000ff38 0x383000fffc000ff3

def z1043 : W := mkw 0x0000104240000000 0x8000010424000000 0xa00474e7c0000000 0x3a00474e7c000000

def z1044 : W := mkw 0x0000104240000000 0x8000010424000000 0x800004e7c0000938 0x3800004e7c000093

def z1045 : W := mkw 0x01f6bed650500006 0xd01f6bed65050000 0x5ce7b4e738780005 0xc5ce7b4e73878000

def z1046 : W := mkw 0x1009410882240269 0x0100941088224026 0xff1ffb18c6648ffe 0xfff1ffb18c6648ff

def z1047 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0xabfc0fe03f80fe0a 0x9abfc0fe03f80fe0

def z1048 : W := mkw 0x7800002100893b70 0x07800002100893b7 0x020000000000fff8 0x0020000000000fff

def z1049 : W := mkw 0x6800106340893910 0x8680010634089391 0xb404f4e7c19f783b 0x5b404f4e7c19f783

def z1050 : W := mkw 0x80fffc567776000c 0xb80fffc567776000 0xfcfffcffffff0007 0xffcfffcffffff000

def z1051 : W := mkw 0x0000104240000000 0x8000010424000000 0x6004f0e7c0000000 0x36004f0e7c000000

def z1052 : W := mkw 0x6800106340893910 0x8680010634089391 0xfc1cf4e7c79f793f 0xffc1cf4e7c79f793

def z1053 : W := mkw 0x600000212d88fd80 0x2600000212d88fd8 0x020000003f80ffcb 0xc020000003f80ffc

def z1054 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xfdffffffc0600004 0xffdffffffc060000

def z1055 : W := mkw 0x01f6bfdec0000007 0xc01f6bfdec000000 0x11e4b7e7c0000000 0x111e4b7e7c000000

def z1056 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0x10e7b00039fb0001 0x010e7b00039fb000

def z1057 : W := mkw 0x80d6a00035520004 0x380d6a0003552000 0x30fcb0003f9b0003 0x030fcb0003f9b000

def z1058 : W := mkw 0x01ffffdeed00c40f 0xe01ffffdeed00c40 0xfffffffffe00f609 0xffffffffffe00f60

def z1059 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0xbffc7fe03f87fe0b 0xdbffc7fe03f87fe0

def z1060 : W := mkw 0x2042801510581180 0x1204280151058118 0xdce3841f387871cd 0xedce3841f387871c

def z1061 : W := mkw 0x01f6bed640000006 0xc01f6bed64000000 0x50e4f4e7c0000000 0x250e4f4e7c000000

def z1062 : W := mkw 0x20628c151858d180 0x120628c151858d18 0x4ae3881f3878f1cd 0xe4ae3881f3878f1c

def z1063 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0xaff80fe03e00fe0a 0xdaff80fe03e00fe0

def z1064 : W := mkw 0x20628c151858d180 0x120628c151858d18 0xfee78cff3878f1cd 0xffee78cff3878f1c

def z1065 : W := mkw 0x6800002100893910 0x0680000210089391 0x000000000004793e 0x4000000000004793

def z1066 : W := mkw 0x20628c151858d180 0x120628c151858d18 0xfffbcf1ffe7cffff 0xffffbcf1ffe7cfff

def z1067 : W := mkw 0x2042800110581100 0x1204280011058110 0xdee38c1f3878f1cd 0xedee38c1f3878f1c

def z1068 : W := mkw 0x0162bfdec0000007 0xc0162bfdec000000 0x8100bfffc0000000 0x38100bfffc000000

def z1069 : W := mkw 0x01f6bed640000006 0xc01f6bed64000000 0x90e4bcff00000000 0x290e4bcff0000000

def z1070 : W := mkw 0x0000104240000000 0x8000010424000000 0xf404f4e7c19f093f 0x7f404f4e7c19f093

def z1071 : W := mkw 0x90dfe108b776026d 0x390dfe108b776026 0x7ffffb183fff8fff 0xc7ffffb183fff8ff

def z1072 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xfdffffffc6000002 0xffdffffffc600000

def z1073 : W := mkw 0x01201fdec0000003 0xc01201fdec000000 0xd5008fffc0000000 0x3d5008fffc000000

def z1074 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0xbffc0fe03fe0ffcf 0xdbffc0fe03fe0ffc

def z1075 : W := mkw 0x01dff3dec000000f 0xc01dff3dec000000 0xed1ffbffc0000000 0x3ed1ffbffc000000

def z1076 : W := mkw 0x01201fdec800c083 0xc01201fdec800c08 0x83000fffc00080c0 0x383000fffc00080c

def z1077 : W := mkw 0x90dfe0003776026c 0x390dfe0003776026 0x7cfff0003fff0e37 0xc7cfff0003fff0e3

def z1078 : W := mkw 0xe80000213ffff990 0x3e80000213ffff99 0x020000003ffff9ff 0xc020000003ffff9f

def z1079 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xfdffffffc1800003 0x7fdffffffc180000

def z1080 : W := mkw 0x01b41fdee5000003 0xe01b41fdee500000 0xbdfc0fffff800003 0xfbdfc0fffff80000

def z1081 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0x7cfff000ffff0137 0xe7cfff000ffff013

def z1082 : W := mkw 0x11ffffdec224026f 0xc11ffffdec224026 0xffffffffc66486c6 0xfffffffffc66486c

def z1083 : W := mkw 0x00f68e9435500002 0x300f68e943550000 0xfdff8fff3ff80007 0xffdff8fff3ff8000

def z1084 : W := mkw 0x81ffffdef776000f 0xf81ffffdef776000 0xffffffffffff8e0f 0xfffffffffffff8e0

def z1085 : W := mkw 0x016bffdec000000f 0xc016bffdec000000 0xed1bffffc0000000 0x3ed1bffffc000000

def z1086 : W := mkw 0x81ffffdef552000f 0xf81ffffdef552000 0xfdfffffff8000000 0x3fdfffffff800000

def z1087 : W := mkw 0x11ffffdec224026f 0xc11ffffdec224026 0x31fcf7e7c6040e32 0x131fcf7e7c6040e3

def z1088 : W := mkw 0x81f6bfdef5520007 0xf81f6bfdef552000 0x91e4bffff99b0001 0x391e4bffff99b000

def z1089 : W := mkw 0x8094000037760000 0x3809400003776000 0x7cfcf0003fff0007 0xc7cfcf0003fff000

def z1090 : W := mkw 0x6800002100893910 0x0680000210089391 0x00000000019f7135 0x000000000019f713

def z1091 : W := mkw 0x01ffffdeed00c40f 0xe01ffffdeed00c40 0xfdfffffff8000000 0x3fdfffffff800000

def z1092 : W := mkw 0x01201fdec0000003 0xc01201fdec000000 0xe5004fffc0000000 0x3e5004fffc000000

def z1093 : W := mkw 0x00629c5640000000 0x800629c564000000 0x10e4b4e700000000 0x010e4b4e70000000

def z1094 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0xbdfc0fe03f807e03 0x1bdfc0fe03f807e0

def z1095 : W := mkw 0x81f6bed675520006 0xf81f6bed67552000 0xf4e4f4e7f99f0007 0x7f4e4f4e7f99f000

def z1096 : W := mkw 0x90dfe108b776026d 0x390dfe108b776026 0x50e7f018f9ff01f5 0x250e7f018f9ff01f

def z1097 : W := mkw 0x80d6a00035520004 0x380d6a0003552000 0x30e4f000399f0003 0x030e4f000399f000

def z1098 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0x33fc07e03f80fe0b 0xd33fc07e03f80fe0

def z1099 : W := mkw 0x81ffffdef776000f 0xf81ffffdef776000 0xfdffffffffff093f 0xffdffffffffff093

def z1100 : W := mkw 0x20628c151858d180 0x120628c151858d18 0xdffb8f1f3e78f7cd 0xedffb8f1f3e78f7c

def z1101 : W := mkw 0x00dff14ac000000d 0x800dff14ac000000 0xfdffffffc0000000 0x3fdffffffc000000

def z1102 : W := mkw 0x4094002025802800 0x2409400202580280 0xbffc0fe03f80fe0b 0xdbffc0fe03f80fe0

def z1103 : W := mkw 0x81ffffded052000f 0xd81ffffded052000 0xfdffffffc01b0000 0x3fdffffffc01b000

def z1104 : W := mkw 0x81fffed66726000e 0xe81fffed66726000 0x30fcf4e707870002 0x030fcf4e70787000

def z1105 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0x8bf80fe03f80fe0b 0xd8bf80fe03f80fe0

def z1106 : W := mkw 0x409402a025802c02 0x2409402a025802c0 0xbdfc07e03f807e0b 0xdbdfc07e03f807e0

def z1107 : W := mkw 0x01ffffded850c08f 0xd01ffffded850c08 0xfdfffffff8000000 0x3fdfffffff800000

def z1108 : W := mkw 0x6800002100893910 0x0680000210089391 0xf404f000c19f793f 0x7f404f000c19f793

def z1109 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xffffffffc06489fe 0xfffffffffc06489f

def z1110 : W := mkw 0x01f6bfdec0000007 0xc01f6bfdec000000 0x10e4b4ffc0000000 0x210e4b4ffc000000

def z1111 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xffffffffc6008600 0xbffffffffc600860

def z1112 : W := mkw 0x6800002100893910 0x0680000210089391 0x00000000019b710d 0x400000000019b710

def z1113 : W := mkw 0x6800002100893910 0x0680000210089391 0x00000000019f7007 0x400000000019f700

def z1114 : W := mkw 0x81bd7fdee726000f 0xe81bd7fdee726000 0xa11c7fffc7870002 0x3a11c7fffc787000

def z1115 : W := mkw 0x80d6a00037760004 0x380d6a0003776000 0x10e4b0003f9f0003 0x010e4b0003f9f000

def z1116 : W := mkw 0x1009410882240269 0x0100941088224026 0xff1b4f18c664ffff 0xfff1b4f18c664fff

def z1117 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0xbffc0fe03e00fe08 0x9bffc0fe03e00fe0

def z1118 : W := mkw 0x01ffffdee500040f 0xe01ffffdee500040 0xfdffffffc6000600 0x3fdffffffc600060

def z1119 : W := mkw 0x01bd7fdec000000f 0xc01bd7fdec000000 0xf51cffffc0000000 0x3f51cffffc000000

def z1120 : W := mkw 0x00628e9400000002 0x000628e940000000 0xdde38fff00000000 0x3dde38fff0000000

def z1121 : W := mkw 0x81dff3caf776000f 0xf81dff3caf776000 0xfdfff7e7ffff0007 0xffdfff7e7ffff000

def z1122 : W := mkw 0x81f6bed675520006 0xf81f6bed67552000 0xbdfcbfe73f9b0003 0xdbdfcbfe73f9b000

def z1123 : W := mkw 0x6800002100893910 0x0680000210089391 0x20004000c19f793f 0x520004000c19f793

def z1124 : W := mkw 0x91ffffdef776026f 0xf91ffffdef776026 0xfdffffffffff0e37 0xffdffffffffff0e3

def z1125 : W := mkw 0x1009410882240269 0x0100941088224026 0xef1f7b18c7e78ffe 0xfef1f7b18c7e78ff

def z1126 : W := mkw 0x01629ed640000002 0xc01629ed64000000 0x10e084e700000000 0x010e084e70000000

def z1127 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0xbfff0ff83fe0fecb 0xdbfff0ff83fe0fec

def z1128 : W := mkw 0x01201ed640000002 0xc01201ed64000000 0x81000fe700000000 0x181000fe70000000

def z1129 : W := mkw 0x00b41ec240000002 0x800b41ec24000000 0xf4e4f4e7c0000000 0x3f4e4f4e7c000000

def z1130 : W := mkw 0x81ffffdeff76c08f 0xf81ffffdeff76c08 0xfffffffffe6080c0 0xbfffffffffe6080c

def z1131 : W := mkw 0x20628c151858d180 0x120628c151858d18 0xfee38c1f3878f9cf 0xffee38c1f3878f9c

def z1132 : W := mkw 0x00f68e9400000002 0x000f68e940000000 0x10e484e700000000 0x010e484e70000000

def z1133 : W := mkw 0x0094000025000000 0x2009400002500000 0x3cfcb0003f9b0003 0xc3cfcb0003f9b000

def z1134 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0xfffcffe0ff9fff3f 0xffffcffe0ff9fff3

def z1135 : W := mkw 0x80d6a00035520004 0x380d6a0003552000 0x50e7b00039fb0005 0x050e7b00039fb000

def z1136 : W := mkw 0x20628c151858d180 0x120628c151858d18 0xfee3cc1ff878f1cd 0xffee3cc1ff878f1c

def z1137 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0x74fcf0003f9f0007 0x474fcf0003f9f000

def z1138 : W := mkw 0x6800106340893910 0x8680010634089391 0xfc07f4e7c1ff793f 0xffc07f4e7c1ff793

def z1139 : W := mkw 0x01b41fdec0000003 0xc01b41fdec000000 0xa11c0fffc0000000 0x3a11c0fffc000000

def z1140 : W := mkw 0x01f6bed640000006 0xc01f6bed64000000 0x3cfcb4e700000000 0x03cfcb4e70000000

def z1141 : W := mkw 0x80dfe108b776000d 0x380dfe108b776000 0x7dfffb183fff0007 0xc7dfffb183fff000

def z1142 : W := mkw 0xe809402137ff3918 0x3e809402137ff391 0xec1b4000ffff793f 0xfec1b4000ffff793

def z1143 : W := mkw 0x90dfe108b776026d 0x390dfe108b776026 0xfdfff300ffff0f3f 0xffdfff300ffff0f3

def z1144 : W := mkw 0x80d6a00037760004 0x380d6a0003776000 0x5ce7b0003fff0007 0xc5ce7b0003fff000

def z1145 : W := mkw 0x81ffffdef776000f 0xf81ffffdef776000 0x31fcf7e7ff9f0003 0x131fcf7e7ff9f000

def z1146 : W := mkw 0x0094000025000000 0x2009400002500000 0xfffcfb00ff9f8f3f 0xffffcfb00ff9f8f3

def z1147 : W := mkw 0x01f6bed640000006 0xc01f6bed64000000 0x50e7b4ff00000000 0x250e7b4ff0000000

def z1148 : W := mkw 0x0000104240000000 0x8000010424000000 0xd40084e7c0000000 0x3d40084e7c000000

def z1149 : W := mkw 0x600000210888fd80 0x0600000210888fd8 0x020000000000ffc8 0x0020000000000ffc

def z1150 : W := mkw 0x1009410882240269 0x0100941088224026 0xab1b4b18c6648ffa 0xbab1b4b18c6648ff

def z1151 : W := mkw 0x00fffc564000000c 0x800fffc564000000 0xfcfffcffc0000000 0x3fcfffcffc000000

def z1152 : W := mkw 0x81dfe11cb776000d 0x781dfe11cb776000 0x7cfff0183fff0007 0xc7cfff0183fff000

def z1153 : W := mkw 0x6800002100893910 0x0680000210089391 0x0000000000007000 0x0000000000000700

def z1154 : W := mkw 0x6800002100893910 0x0680000210089391 0x0200000001fff9ff 0xc0200000001fff9f

def z1155 : W := mkw 0x81ffffdef776000f 0xf81ffffdef776000 0xfdfffffffe7f0004 0xbfdfffffffe7f000

def z1156 : W := mkw 0x90dfe108b776026d 0x390dfe108b776026 0x7dfff318ffff0ff7 0xf7dfff318ffff0ff

def z1157 : W := mkw 0x314bf15fd27c13ed 0xd314bf15fd27c13e 0x4003f01fc07c01f4 0x24003f01fc07c01f

def z1158 : W := mkw 0x6800002118d9f990 0x16800002118d9f99 0xee034818f9fff9ff 0xfee034818f9fff9f

def z1159 : W := mkw 0x6800106340893910 0x8680010634089391 0xb004f4e7c19f793b 0x3b004f4e7c19f793

def z1160 : W := mkw 0x01201fdec0000003 0xc01201fdec000000 0xcd030fffc0000000 0x3cd030fffc000000

def z1161 : W := mkw 0x600000213dd8fd80 0x3600000213dd8fd8 0x0200000039f8f1cd 0xc0200000039f8f1c

def z1162 : W := mkw 0x6800106340893910 0x8680010634089391 0xf604f4e7c79fff3f 0xff604f4e7c79fff3

def z1163 : W := mkw 0x01201fdec800c003 0xc01201fdec800c00 0x9fe00ffff800f009 0xf9fe00ffff800f00

def z1164 : W := mkw 0x00fffec24000000e 0x800fffec24000000 0xfdffffe7c0000000 0x3fdffffe7c000000

def z1165 : W := mkw 0x01ffffdec224000f 0xc01ffffdec224000 0xfdffffffc6040002 0x3fdffffffc604000

def z1166 : W := mkw 0x00ffee940000000e 0x000ffee940000000 0xfdffffff00000000 0x3fdffffff0000000

def z1167 : W := mkw 0x6800002100893910 0x0680000210089391 0xe4004000c004793e 0x7e4004000c004793

def z1168 : W := mkw 0x20200c150808d180 0x020200c150808d18 0xdee30c1f3860f1cd 0xedee30c1f3860f1c

def z1169 : W := mkw 0x00b41ec240000002 0x800b41ec24000000 0xfffcffe7c6048f3e 0xffffcffe7c6048f3

def z1170 : W := mkw 0x6800002100893910 0x0680000210089391 0x00000000019b7939 0x000000000019b793

def z1171 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0x38fff0003fff0003 0x838fff0003fff000

def z1172 : W := mkw 0x90dfe108b776026d 0x390dfe108b776026 0x7ffffb18ffff87f7 0xe7ffffb18ffff87f

def z1173 : W := mkw 0xe8d6a02135db3914 0x3e8d6a02135db391 0x10e4b000399b7001 0x010e4b000399b700

def z1174 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0x7cfff000ffff0837 0xd7cfff000ffff083

def z1175 : W := mkw 0x01fffed64000000e 0xc01fffed64000000 0x30fcf4e700000000 0x030fcf4e70000000

def z1176 : W := mkw 0x11295fdec224026b 0xc11295fdec224026 0xff1fffffc6648ffe 0xfff1fffffc6648ff

def z1177 : W := mkw 0x6800106340893910 0x8680010634089391 0x00007000c19f793f 0x400007000c19f793

def z1178 : W := mkw 0x016bfd5ec000000d 0xc016bfd5ec000000 0xfce7fcffc0000000 0x3fce7fcffc000000

def z1179 : W := mkw 0x7800002102ad3b70 0x07800002102ad3b7 0x00000000079f7f3f 0x400000000079f7f3

def z1180 : W := mkw 0x01f6bed640000006 0xc01f6bed64000000 0x18e7bcff00000000 0x018e7bcff0000000

def z1181 : W := mkw 0x80dfe0143776000c 0x380dfe0143776000 0x7cfff01f3fff0007 0xe7cfff01f3fff000

def z1182 : W := mkw 0x81ffffdef776000f 0xf81ffffdef776000 0x7dfff7e7ffff0007 0xd7dfff7e7ffff000

def z1183 : W := mkw 0x20628c151858d180 0x120628c151858d18 0xdee38c1ff878f9fd 0xfdee38c1ff878f9f

def z1184 : W := mkw 0x119d73cac224026f 0xc119d73cac224026 0xff1fffffc6648ffe 0xfff1fffffc6648ff

def z1185 : W := mkw 0x1000114ac0000261 0x81000114ac000026 0x83000fffc0008ff8 0x383000fffc0008ff

def z1186 : W := mkw 0x0000104240000000 0x8000010424000000 0x1004b4e7019b0001 0x01004b4e7019b000

def z1187 : W := mkw 0x6800002100893910 0x0680000210089391 0x00000000019b780b 0x400000000019b780

def z1188 : W := mkw 0x0000104240000000 0x8000010424000000 0xf404f4e7c000080a 0x7f404f4e7c000080

def z1189 : W := mkw 0x09ffffdec001001f 0xc09ffffdec001001 0xfdffffffc0070030 0x3fdffffffc007003

def z1190 : W := mkw 0x91ffffdef776026f 0xf91ffffdef776026 0xfffffffffe6086c0 0xbfffffffffe6086c

def z1191 : W := mkw 0x116bdfdec224026b 0xc116bdfdec224026 0xfffbcfffc6648ffe 0xffffbcfffc6648ff

def z1192 : W := mkw 0x009d70424000000c 0x8009d70424000000 0xf41cf4e7c0000000 0x3f41cf4e7c000000

def z1193 : W := mkw 0x119d73cac224026f 0xc119d73cac224026 0xf51cf7e7c6040f3e 0x7f51cf7e7c6040f3

def z1194 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0x7efff0003fff81cf 0xc7efff0003fff81c

def z1195 : W := mkw 0x384bd15fd27d13f9 0x9384bd15fd27d13f 0x4003f01fc07f01f4 0x24003f01fc07f01f

def z1196 : W := mkw 0x81ffffded276000f 0xd81ffffded276000 0xfdfffffff87f0005 0xffdfffffff87f000

def z1197 : W := mkw 0x0042904250500000 0x9004290425050000 0xfce7f4e7f8780005 0xffce7f4e7f878000

def z1198 : W := mkw 0x600000213dd8fd80 0x3600000213dd8fd8 0xef1b0b183ff8ffcf 0xfef1b0b183ff8ffc

def z1199 : W := mkw 0x90dfe0003776026c 0x390dfe0003776026 0xfefff8183fff8fff 0xefefff8183fff8ff

def z1200 : W := mkw 0x1009514ac2240269 0x81009514ac224026 0xef1b4fffc6648ffe 0xfef1b4fffc6648ff

def z1201 : W := mkw 0x01201fdec0000003 0xc01201fdec000000 0x83000fffc0008e08 0x383000fffc0008e0

def z1202 : W := mkw 0x01ffffded050000f 0xd01ffffded050000 0xfffffffff87881cd 0xffffffffff87881c

def z1203 : W := mkw 0x68201ee34889fd12 0x868201ee34889fd1 0x000004e700007000 0x0000004e70000700

def z1204 : W := mkw 0x90d6a00037760264 0x390d6a0003776026 0x12e4b0003fff8fff 0xc12e4b0003fff8ff

def z1205 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xfdffffffc0007009 0x7fdffffffc000700

def z1206 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xfdffffffc01f0004 0x3fdffffffc01f000

def z1207 : W := mkw 0x1000010880000261 0x0100001088000026 0xef1b0b18c6608ffe 0xfef1b0b18c6608ff

def z1208 : W := mkw 0x20628c151858d180 0x120628c151858d18 0xdee38c1f3860f1c8 0xadee38c1f3860f1c

def z1209 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0x59ffffffc0000000 0x259ffffffc000000

def z1210 : W := mkw 0x6800106340893910 0x8680010634089391 0x7404f4e7c19f7137 0x67404f4e7c19f713

def z1211 : W := mkw 0x01f6bed640000006 0xc01f6bed64000000 0xdee7bcff006081cc 0xedee7bcff006081c

def z1212 : W := mkw 0x014bf15ec000000d 0xc014bf15ec000000 0x5007f4ffc0000000 0x25007f4ffc000000

def z1213 : W := mkw 0x01ffffded850c00f 0xd01ffffded850c00 0xfffffffff878f00d 0xffffffffff878f00

def z1214 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xfdffffffc0040134 0x3fdffffffc004013

def z1215 : W := mkw 0x01b43fdec0000007 0xc01b43fdec000000 0x81043fffc0000000 0x381043fffc000000

def z1216 : W := mkw 0x01bd7fcac000000f 0xc01bd7fcac000000 0xfdfcffe7c0000000 0x3fdfcffe7c000000

def z1217 : W := mkw 0x6000002118d8fd80 0x16000002118d8fd8 0x020000003878ffcd 0xc020000003878ffc

def z1218 : W := mkw 0x01295fdec000000b 0xc01295fdec000000 0xc1034fffc0000000 0x3c1034fffc000000

def z1219 : W := mkw 0x0109714ac000000d 0xc0109714ac000000 0xf404f4e7c0000000 0x3f404f4e7c000000

def z1220 : W := mkw 0xe800002112ff3910 0x1e800002112ff391 0x0000000001ff793f 0x40000000001ff793

def z1221 : W := mkw 0x019432c240000006 0xc019432c24000000 0x1004b4e700000000 0x01004b4e70000000

def z1222 : W := mkw 0x11295fdec224026b 0xc11295fdec224026 0x8b1b0fffc66086c0 0xb8b1b0fffc66086c

def z1223 : W := mkw 0x11ffffdec000026f 0xc11ffffdec000026 0xffffffffc00086c0 0x3ffffffffc00086c

def z1224 : W := mkw 0x40628c342d80ec00 0x240628c342d80ec0 0xdee38c1f3f80fe0b 0xedee38c1f3f80fe0

def z1225 : W := mkw 0x01f6bed66d00c406 0xe01f6bed66d00c40 0x1bfcbfe73e008600 0x81bfcbfe73e00860

def z1226 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0xbffc0ff83f80ffcb 0xfbffc0ff83f80ffc

def z1227 : W := mkw 0x01f6bed640000006 0xc01f6bed64000000 0xfce7fcffc0000000 0x3fce7fcffc000000

def z1228 : W := mkw 0x68200c210889f910 0x068200c210889f91 0x9ee00c00399ff93f 0xc9ee00c00399ff93

def z1229 : W := mkw 0x6800002125893910 0x2680000212589391 0x000000003f9f793f 0xc000000003f9f793

def z1230 : W := mkw 0x80dff0427776000c 0xb80dff0427776000 0x7cfff4e73fff0007 0xc7cfff4e73fff000

def z1231 : W := mkw 0x80d6a00035520004 0x380d6a0003552000 0x5ce7b000399b0001 0x05ce7b000399b000

def z1232 : W := mkw 0xf8094129b7ff3b79 0x3f8094129b7ff3b7 0xef1b4b18ffffffff 0xfef1b4b18fffffff

def z1233 : W := mkw 0x004bc00012740008 0x1004bc0001274000 0x7cfff0003fff0007 0xc7cfff0003fff000

def z1234 : W := mkw 0x0142b05640000004 0xc0142b0564000000 0x1004b4e700000000 0x01004b4e70000000

def z1235 : W := mkw 0x20628e951858d182 0x120628e951858d18 0xdfe38fff3878f1cd 0xfdfe38fff3878f1c

def z1236 : W := mkw 0x01bd7fdec000000f 0xc01bd7fdec000000 0xed1f7fffc0000000 0x3ed1f7fffc000000

def z1237 : W := mkw 0x11bd5fdec224026b 0xc11bd5fdec224026 0xffff4fffc6648ffe 0xfffff4fffc6648ff

def z1238 : W := mkw 0x01f6bed665000006 0xe01f6bed66500000 0x3cfcb4e73f800003 0xc3cfcb4e73f80000

def z1239 : W := mkw 0x11ffffdec224026f 0xc11ffffdec224026 0xfdffffffc6640e36 0xffdffffffc6640e3

def z1240 : W := mkw 0x11ffffdec224026f 0xc11ffffdec224026 0xffffffffc66487f4 0xbffffffffc66487f

def z1241 : W := mkw 0x01ffffdee724000f 0xe01ffffdee724000 0xfdffffffffe40007 0xffdffffffffe4000

def z1242 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0xfffc4fe0ff80fe0b 0xffffc4fe0ff80fe0

def z1243 : W := mkw 0x00629c5640000000 0x800629c564000000 0xdce38cffc0000000 0x3dce38cffc000000

def z1244 : W := mkw 0x80dff0427776000c 0xb80dff0427776000 0xfcfff4e7fe600000 0xbfcfff4e7fe60000

def z1245 : W := mkw 0x81ffffdeff76c40f 0xf81ffffdeff76c40 0xffffffffffff8607 0xfffffffffffff860

def z1246 : W := mkw 0x680000210889fd10 0x0680000210889fd1 0x020000000000ff38 0x0020000000000ff3

def z1247 : W := mkw 0x90dfe108b776026d 0x390dfe108b776026 0xfffffb00ffff8e3f 0xdfffffb00ffff8e3

def z1248 : W := mkw 0x11ffffdeda74c2ef 0xd11ffffdeda74c2e 0xfffffffffe648ffe 0xffffffffffe648ff

def z1249 : W := mkw 0x81ffffdef776000f 0xf81ffffdef776000 0xfdffffffff9f0003 0x3fdffffffff9f000

def z1250 : W := mkw 0x680000212d89fd10 0x2680000212d89fd1 0x020000003f80ff3b 0xc020000003f80ff3

def z1251 : W := mkw 0x90dfe108b776026d 0x390dfe108b776026 0x7ffffb18ffff8ef7 0xd7ffffb18ffff8ef

def z1252 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xffffffffc0008008 0xfffffffffc000800

def z1253 : W := mkw 0xa062ac15185ad184 0x1a062ac15185ad18 0xdee3bc1f387bf1cd 0xedee3bc1f387bf1c

def z1254 : W := mkw 0x1009410882240269 0x0100941088224026 0x2b1b4b18c6648ffe 0xd2b1b4b18c6648ff

def z1255 : W := mkw 0x6800106340893910 0x8680010634089391 0xfe04fce7c19ff93f 0xffe04fce7c19ff93

def z1256 : W := mkw 0x01dff3cac000000f 0xc01dff3cac000000 0xfdfff7e7c0000000 0x3fdfff7e7c000000

def z1257 : W := mkw 0x81ffffded276000f 0xd81ffffded276000 0xfdffffffc0600000 0x3fdffffffc060000

def z1258 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0xfcfff8183fff0007 0xefcfff8183fff000

def z1259 : W := mkw 0x019432c240000006 0xc019432c24000000 0xf404f4e7c0000000 0x3f404f4e7c000000

def z1260 : W := mkw 0x01ffffded850c08f 0xd01ffffded850c08 0xfffffffff87880c5 0xffffffffff87880c

def z1261 : W := mkw 0x11dff3dec224026f 0xc11dff3dec224026 0xef1ffbffc6648ffe 0xfef1ffbffc6648ff

def z1262 : W := mkw 0x01ffffded050000f 0xd01ffffded050000 0xfdffffffc0780004 0x3fdffffffc078000

def z1263 : W := mkw 0x01fffed64000000e 0xc01fffed64000000 0x18ffb4e700000000 0x018ffb4e70000000

def z1264 : W := mkw 0x01b41ed640000002 0xc01b41ed64000000 0x10e404e700000000 0x010e404e70000000

def z1265 : W := mkw 0x01201fdec0000003 0xc01201fdec000000 0x000004ffc0000000 0x2000004ffc000000

def z1266 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xffffffffc6608fce 0xfffffffffc6608fc

def z1267 : W := mkw 0x00629c5640000000 0x800629c564000000 0xf4e4f4e7c0000000 0x3f4e4f4e7c000000

def z1268 : W := mkw 0x00bd5fcac000000b 0x800bd5fcac000000 0xfdffffffc0000000 0x3fdffffffc000000

def z1269 : W := mkw 0x0009514ac0000009 0x80009514ac000000 0xf407f4ffc0000000 0x3f407f4ffc000000

def z1270 : W := mkw 0x68201c774889f990 0x868201c774889f99 0x000004e700007000 0x0000004e70000700

def z1271 : W := mkw 0x20b40e811858d182 0x120b40e811858d18 0xbffc0fe03878f1cd 0xdbffc0fe03878f1c

def z1272 : W := mkw 0x00b40e800800c002 0x000b40e800800c00 0xbffc0fe03e00fe0b 0xdbffc0fe03e00fe0

def z1273 : W := mkw 0x90dfe0003776026c 0x390dfe0003776026 0x7efff0003fff86c7 0xc7efff0003fff86c

def z1274 : W := mkw 0x109d4108a7240269 0x2109d4108a724026 0xfffffb18ffff8fff 0xffffffb18ffff8ff

def z1275 : W := mkw 0x01201fdec0000003 0xc01201fdec000000 0xc100ffffc0000000 0x3c100ffffc000000

def z1276 : W := mkw 0x20628c151858d180 0x120628c151858d18 0xdee38c1f3e78ffcf 0xedee38c1f3e78ffc

def z1277 : W := mkw 0x1009410882240269 0x0100941088224026 0xef1b4b18c6608ff8 0xbef1b4b18c6608ff

def z1278 : W := mkw 0x20628c151858d180 0x120628c151858d18 0x5ee38c1f3878f0c5 0xc5ee38c1f3878f0c

def z1279 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0xfefff818ffff89ff 0xffefff818ffff89f

def z1280 : W := mkw 0x80dfe108b776000d 0x380dfe108b776000 0xfffffb18ffff8e0f 0xffffffb18ffff8e0

def z1281 : W := mkw 0x0042800010500000 0x1004280001050000 0x74e4f000399f0007 0x474e4f000399f000

def z1282 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0x30fcf0003fff0007 0xc30fcf0003fff000

def z1283 : W := mkw 0x01f6bed64800c006 0xc01f6bed64800c00 0x9ee4bce73800f009 0xc9ee4bce73800f00

def z1284 : W := mkw 0x01dff3dec000000f 0xc01dff3dec000000 0x211cf3e7c0000000 0x1211cf3e7c000000

def z1285 : W := mkw 0x80fffec27776000e 0xb80fffec27776000 0xfdffffe7ffff0007 0xffdffffe7ffff000

def z1286 : W := mkw 0x0000104240000000 0x8000010424000000 0xb404b4e700000000 0x1b404b4e70000000

def z1287 : W := mkw 0x0000104240000000 0x8000010424000000 0xe40044e7c0000000 0x3e40044e7c000000

def z1288 : W := mkw 0x01201ed640000002 0xc01201ed64000000 0xf404f4e7c0000000 0x3f404f4e7c000000

def z1289 : W := mkw 0x00201ec240000002 0x800201ec24000000 0xf504ffe7c0000000 0x3f504ffe7c000000

def z1290 : W := mkw 0x6800002100893910 0x0680000210089391 0x1004b000019f793f 0x41004b000019f793

def z1291 : W := mkw 0x01201fdec0000003 0xc01201fdec000000 0x83000fffc00081c8 0x383000fffc00081c

def z1292 : W := mkw 0x81fffed67776000e 0xf81fffed67776000 0xfcfff4e7ffff0007 0xffcfff4e7ffff000

def z1293 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0xb3fc0fe03f80fe0b 0x1b3fc0fe03f80fe0

def z1294 : W := mkw 0x600000213dd8fd80 0x3600000213dd8fd8 0x0000000039987001 0x0000000003998700

def z1295 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xfdffffffc1870002 0x3fdffffffc187000

def z1296 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0xbffc0fe03f80f601 0x9bffc0fe03f80f60

def z1297 : W := mkw 0x7809412982ad3b79 0x07809412982ad3b7 0x0b1b0b1807ffffff 0xc0b1b0b1807fffff

def z1298 : W := mkw 0x01dff3dec000000f 0xc01dff3dec000000 0x7dfff3ffc0000000 0x37dfff3ffc000000

def z1299 : W := mkw 0x28628c151859d190 0x128628c151859d19 0xdee38c1f387ff1fd 0xedee38c1f387ff1f

def z1300 : W := mkw 0x01201fdec800c403 0xc01201fdec800c40 0x83000fffc0008600 0x383000fffc000860

def z1301 : W := mkw 0x68b40ea12d89fd12 0x268b40ea12d89fd1 0x0bf80b003f9fff3f 0xc0bf80b003f9fff3

def z1302 : W := mkw 0x01fffed64000000e 0xc01fffed64000000 0xfcfff4e7c0000000 0x3fcfff4e7c000000

def z1303 : W := mkw 0x91ffffded276026f 0xd91ffffded276026 0xffffffffc67f8ffe 0xfffffffffc67f8ff

def z1304 : W := mkw 0x01f6bed640000006 0xc01f6bed64000000 0xd4e4b4e700000000 0x2d4e4b4e70000000

def z1305 : W := mkw 0x81f6bed665020006 0xe81f6bed66502000 0x10e4b4e701830000 0x010e4b4e70183000

def z1306 : W := mkw 0x680000212d89fd10 0x2680000212d89fd1 0xef184b00ff9fff3f 0xfef184b00ff9fff3

def z1307 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xdce7fcffc0000000 0x2dce7fcffc000000

def z1308 : W := mkw 0x80d6a00035520004 0x380d6a0003552000 0x7cfcf0003f9f0007 0xc7cfcf0003f9f000

def z1309 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xfdffffffc19f093f 0x7fdffffffc19f093

def z1310 : W := mkw 0x11ffffdeca24c26f 0xc11ffffdeca24c26 0xfffffffffe64ffff 0xffffffffffe64fff

def z1311 : W := mkw 0x11295fdec224026b 0xc11295fdec224026 0xc1034fffc06401f4 0x3c1034fffc06401f

def z1312 : W := mkw 0x01b41ed640000002 0xc01b41ed64000000 0xbdfc0fe700000000 0x1bdfc0fe70000000

def z1313 : W := mkw 0x01f6bed65850c086 0xd01f6bed65850c08 0x1ae7bcff386080c0 0x81ae7bcff386080c

def z1314 : W := mkw 0x11ffffdec224026f 0xc11ffffdec224026 0xffffffffc06481fc 0xfffffffffc06481f

def z1315 : W := mkw 0x6842802118d9f990 0x16842802118d9f99 0x7ee7f00039fff9ff 0xc7ee7f00039fff9f

def z1316 : W := mkw 0xe8dfe0213ffff99c 0x3e8dfe0213ffff99 0x7efff0003ffff9ff 0xc7efff0003ffff9f

def z1317 : W := mkw 0x1009410882240269 0x0100941088224026 0x8b1b0b18c6648ffe 0xf8b1b0b18c6648ff

def z1318 : W := mkw 0x81ffffdef776000f 0xf81ffffdef776000 0x89fb0ffffe600000 0xb89fb0ffffe60000

def z1319 : W := mkw 0x6800106340893910 0x8680010634089391 0xf407f4ffc1ff79ff 0x7f407f4ffc1ff79f

def z1320 : W := mkw 0x01201fdec0000003 0xc01201fdec000000 0x9de00fffc0000000 0x39de00fffc000000

def z1321 : W := mkw 0x11ffffdec224026f 0xc11ffffdec224026 0xffffffffc6048ffa 0x3ffffffffc6048ff

def z1322 : W := mkw 0x01f6bed640000006 0xc01f6bed64000000 0x9ce4bce700000000 0x09ce4bce70000000

def z1323 : W := mkw 0x01ffffdee500000f 0xe01ffffdee500000 0xfdfffffffe000000 0xbfdfffffffe00000

def z1324 : W := mkw 0x10dff14ac224026d 0x810dff14ac224026 0xffffffffc6648ffe 0xfffffffffc6648ff

def z1325 : W := mkw 0x6800106340893910 0x8680010634089391 0xd004f4e7c19f793d 0x3d004f4e7c19f793

def z1326 : W := mkw 0x80d6a00035520004 0x380d6a0003552000 0x54e4b000399b0005 0x454e4b000399b000

def z1327 : W := mkw 0x6000002100883900 0x0600000210088390 0x000000000198790f 0x4000000000198790

def z1328 : W := mkw 0x6800106340893910 0x8680010634089391 0xf51cf7e7c79f7f3f 0x7f51cf7e7c79f7f3

def z1329 : W := mkw 0x11ffffdec224026f 0xc11ffffdec224026 0xfdffffffc6000600 0x3fdffffffc600060

def z1330 : W := mkw 0x01ffffdee500000f 0xe01ffffdee500000 0xfdfffffff9800001 0x3fdfffffff980000

def z1331 : W := mkw 0x6800106340893910 0x8680010634089391 0x3004f4e7c19f793f 0x53004f4e7c19f793

def z1332 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0xfffc4fe03f84fe0f 0xdfffc4fe03f84fe0

def z1333 : W := mkw 0x0000104240000000 0x8000010424000000 0xf404f4e7c19b0001 0x3f404f4e7c19b000

def z1334 : W := mkw 0x01f6bed640000006 0xc01f6bed64000000 0x19fcbfe700000000 0x019fcbfe70000000

def z1335 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0xffff0fe03fe0fe0f 0xdffff0fe03fe0fe0

def z1336 : W := mkw 0x6800002100893910 0x0680000210089391 0x4000f000019f793f 0x44000f000019f793

def z1337 : W := mkw 0x6800002100893910 0x0680000210089391 0x80000000c0007938 0x380000000c000793

def z1338 : W := mkw 0x11ffffdec000026f 0xc11ffffdec000026 0xfdffffffc0000e30 0x3fdffffffc0000e3

def z1339 : W := mkw 0x780000212fadff70 0x2780000212fadff7 0x020000003fffffff 0xc020000003ffffff

def z1340 : W := mkw 0x0000114ac0000001 0x80000114ac000000 0xf504ffffc0000000 0x3f504ffffc000000

def z1341 : W := mkw 0x00629c5650500000 0x900629c565050000 0xfce7fcfff9ff0007 0xffce7fcfff9ff000

def z1342 : W := mkw 0x80dfe0003552000c 0x380dfe0003552000 0x30fcf000399b0001 0x030fcf000399b000

def z1343 : W := mkw 0x80d6a00035520004 0x380d6a0003552000 0x10e4b00039fb0005 0xc10e4b00039fb000

def z1344 : W := mkw 0x20628c151858d180 0x120628c151858d18 0xcee30c1f3860f1cc 0xecee30c1f3860f1c

def z1345 : W := mkw 0x680000210889f910 0x0680000210889f91 0x02000000399ff93f 0xc02000000399ff93

def z1346 : W := mkw 0x6800002100893910 0x0680000210089391 0x54008000019f793f 0x454008000019f793

def z1347 : W := mkw 0x1009410882240269 0x0100941088224026 0xef1bfb18c67f8ffe 0xfef1bfb18c67f8ff

def z1348 : W := mkw 0x20628c151858d180 0x120628c151858d18 0xdee38c1f3878f0c1 0xadee38c1f3878f0c

def z1349 : W := mkw 0x1009410882240269 0x0100941088224026 0x6b1b4b18c6648ff6 0xb6b1b4b18c6648ff

def z1350 : W := mkw 0x80d6a00035520004 0x380d6a0003552000 0x18e7b00039fb0001 0x818e7b00039fb000

def z1351 : W := mkw 0x91ffffdef776026f 0xf91ffffdef776026 0xffffffffffff86c7 0xfffffffffffff86c

def z1352 : W := mkw 0x81ffffded276000f 0xd81ffffded276000 0xfdffffffc67f0006 0xffdffffffc67f000

def z1353 : W := mkw 0x6800106340893910 0x8680010634089391 0xe004f4e7c19f793e 0x3e004f4e7c19f793

def z1354 : W := mkw 0x0009514ac2240009 0x80009514ac224000 0xfd1fffffc7ff0007 0xffd1fffffc7ff000

def z1355 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0x3cfcf0003f9f0003 0xc3cfcf0003f9f000

def z1356 : W := mkw 0x00201ec240000002 0x800201ec24000000 0x81000fe7c0000000 0x381000fe7c000000

def z1357 : W := mkw 0x01dff15ec000000d 0xc01dff15ec000000 0xfcfff4ffc0000000 0x3fcfff4ffc000000

def z1358 : W := mkw 0x01bd7fdec000000f 0xc01bd7fdec000000 0xbdfc7fffc0000000 0x3bdfc7fffc000000

def z1359 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xbdff0fffc0000000 0x3bdff0fffc000000

def z1360 : W := mkw 0x81dfe388b776000f 0x781dfe388b776000 0x7dfff3003fff0007 0xc7dfff3003fff000

def z1361 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xffffffffc06080c0 0xbffffffffc06080c

def z1362 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0x10fcb0003f9b0001 0x010fcb0003f9b000

def z1363 : W := mkw 0x68201c774889f990 0x868201c774889f99 0x82000cff0000f1c8 0x282000cff0000f1c

def z1364 : W := mkw 0x40b40eb42d80ec02 0x240b40eb42d80ec0 0xbffc0fff3f80fe0b 0xfbffc0fff3f80fe0

def z1365 : W := mkw 0x6800002118d9f990 0x16800002118d9f99 0x00000000399f793f 0x400000000399f793

def z1366 : W := mkw 0x90dfe108b776026d 0x390dfe108b776026 0x7efff018ffff8fff 0xe7efff018ffff8ff

def z1367 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0x7dfff3003fff0e07 0xd7dfff3003fff0e0

def z1368 : W := mkw 0x11ffffdeef24c66f 0xe11ffffdeef24c66 0xfffffffffe6086c0 0xbfffffffffe6086c

def z1369 : W := mkw 0x11201fdec0000263 0xc11201fdec000026 0xf704ffffc0048ffe 0x7f704ffffc0048ff

def z1370 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xfdffffffc0040006 0x7fdffffffc004000

def z1371 : W := mkw 0x01201fdec0000003 0xc01201fdec000000 0xaf180fffc6008e0a 0xfaf180fffc6008e0

def z1372 : W := mkw 0x01201fdec0000003 0xc01201fdec000000 0x010007e7c0000000 0x1010007e7c000000

def z1373 : W := mkw 0x11ffffdec224026f 0xc11ffffdec224026 0xffffffffc6608eca 0xfffffffffc6608ec

def z1374 : W := mkw 0x0000104240000000 0x8000010424000000 0xfe07fcffc06081cc 0xffe07fcffc06081c

def z1375 : W := mkw 0x01ffffdefd50c48f 0xf01ffffdefd50c48 0xfffffffffe6086c0 0xbfffffffffe6086c

def z1376 : W := mkw 0x80dfe0003552000c 0x380dfe0003552000 0x7cfff00039fb0005 0xc7cfff00039fb000

def z1377 : W := mkw 0x01f6bed640000006 0xc01f6bed64000000 0xfdfcffe7c0000000 0x3fdfcffe7c000000

def z1378 : W := mkw 0x6800106340893910 0x8680010634089391 0x1004f4e7c19f7031 0x01004f4e7c19f703

def z1379 : W := mkw 0x019d73cac000000f 0xc019d73cac000000 0xfd1fffffc0000000 0x3fd1fffffc000000

def z1380 : W := mkw 0x0142b05640000004 0xc0142b0564000000 0xf404f4e7c0000000 0x3f404f4e7c000000

def z1381 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0x7ffffb003fff8607 0xc7ffffb003fff860

def z1382 : W := mkw 0x01629fdec0000003 0xc01629fdec000000 0xc1038fffc0000000 0x3c1038fffc000000

def z1383 : W := mkw 0x006bdd5ec0000009 0x8006bdd5ec000000 0xfdffffffc0000000 0x3fdffffffc000000

def z1384 : W := mkw 0x1009410882240269 0x0100941088224026 0xe31b4b18c6648ffe 0x3e31b4b18c6648ff

def z1385 : W := mkw 0x01ffffdec224000f 0xc01ffffdec224000 0xfdffffffc664093e 0xffdffffffc664093

def z1386 : W := mkw 0x90dfe108b776026d 0x390dfe108b776026 0x7cfff000ffff0037 0xc7cfff000ffff003

def z1387 : W := mkw 0x00201c5640000000 0x800201c564000000 0xf404fcffc0000000 0x3f404fcffc000000

def z1388 : W := mkw 0x00dfe0001050000c 0x100dfe0001050000 0x7cfff00039ff0007 0xc7cfff00039ff000

def z1389 : W := mkw 0x01f6bed640000006 0xc01f6bed64000000 0x5ce7b4e700000000 0x05ce7b4e70000000

def z1390 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0x5cffb0003ffb0005 0xc5cffb0003ffb000

def z1391 : W := mkw 0x20628c151858d180 0x120628c151858d18 0xfefb8c1f3e78f1cf 0xefefb8c1f3e78f1c

def z1392 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0x10e4f000399f0001 0x010e4f000399f000

def z1393 : W := mkw 0x90dfe108b776026d 0x390dfe108b776026 0xfdfffb18ffff01f7 0xffdfffb18ffff01f

def z1394 : W := mkw 0x700000213ffcffe0 0x3700000213ffcffe 0x020000003ffcffff 0xc020000003ffcfff

def z1395 : W := mkw 0x116bffdec224026f 0xc116bffdec224026 0xc303ffffc0648ffc 0x3c303ffffc0648ff

def z1396 : W := mkw 0x00b41ec240000002 0x800b41ec24000000 0xbdfcbfe700000000 0x1bdfcbfe70000000

def z1397 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0xbffcbfe03f9bfe0b 0xdbffcbfe03f9bfe0

def z1398 : W := mkw 0x01f6bed640000006 0xc01f6bed64000000 0x90e4b4e7c0000000 0x390e4b4e7c000000

def z1399 : W := mkw 0x00d6800035500000 0x300d680003550000 0x7cfff0003fff0007 0xc7cfff0003fff000

def z1400 : W := mkw 0x81ffffdef776000f 0xf81ffffdef776000 0xfdfffffffe780005 0xffdfffffffe78000

def z1401 : W := mkw 0x40b40eb42d80ec82 0x240b40eb42d80ec8 0xbffc0ff83f80fecb 0xdbffc0ff83f80fec

def z1402 : W := mkw 0x01f6bed640000006 0xc01f6bed64000000 0x30e4f4e7c0000000 0x130e4f4e7c000000

def z1403 : W := mkw 0xe84be02112ff391c 0x1e84be02112ff391 0x4003f00001ff793f 0x44003f00001ff793

def z1404 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0x11fc07e03f807601 0x011fc07e03f80760

def z1405 : W := mkw 0x0009514ac0000009 0x80009514ac000000 0xed1b4fffc0000000 0x3ed1b4fffc000000

def z1406 : W := mkw 0x20628c151858d180 0x120628c151858d18 0xdce38c1f387871c5 0x2dce38c1f387871c

def z1407 : W := mkw 0x6800002100893910 0x0680000210089391 0x00000000001f793c 0x000000000001f793

def z1408 : W := mkw 0x20628c151858d180 0x120628c151858d18 0xdee7bc1f39fbf1cd 0xedee7bc1f39fbf1c

def z1409 : W := mkw 0x01f6bfdec0000007 0xc01f6bfdec000000 0xbdfcbfffc0000000 0x3bdfcbfffc000000

def z1410 : W := mkw 0x11201fdec0000263 0xc11201fdec000026 0x83000fffc00086c0 0x383000fffc00086c

def z1411 : W := mkw 0x016bdfdec000000b 0xc016bdfdec000000 0xfdfbcfffc0000000 0x3fdfbcfffc000000

def z1412 : W := mkw 0x11bd7fdec224026f 0xc11bd7fdec224026 0xa31c7fffc6048ffa 0x3a31c7fffc6048ff

def z1413 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xe11fffffc0000000 0x3e11fffffc000000

def z1414 : W := mkw 0x70094129bffcffe9 0x370094129bffcffe 0xef1b4b18fffcffff 0xfef1b4b18fffcfff

def z1415 : W := mkw 0x0000104240000000 0x8000010424000000 0xf404f4e7c0180005 0x7f404f4e7c018000

def z1416 : W := mkw 0x6800002100893910 0x0680000210089391 0x94000400019f793f 0x494000400019f793

def z1417 : W := mkw 0x81ffffdef776000f 0xf81ffffdef776000 0xfdffffffffe70002 0xbfdffffffffe7000

def z1418 : W := mkw 0x00ffcf9c8000000b 0x000ffcf9c8000000 0xfdffcfffc0000000 0x3fdffcfffc000000

def z1419 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0x5ce7f00039ff0005 0xc5ce7f00039ff000

def z1420 : W := mkw 0x01f6bed640000006 0xc01f6bed64000000 0x74e4f4e700000000 0x074e4f4e70000000

def z1421 : W := mkw 0x68dfe0210089391c 0x068dfe0210089391 0x7cfff000019f793f 0x47cfff000019f793

def z1422 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0xb5fc07e03f807e0b 0x5b5fc07e03f807e0

def z1423 : W := mkw 0x0009514ac0000009 0x80009514ac000000 0xf51cf7e7c0000000 0x3f51cf7e7c000000

def z1424 : W := mkw 0x11ffffdec000026f 0xc11ffffdec000026 0xffffffffc0048ffe 0x7ffffffffc0048ff

def z1425 : W := mkw 0x6800106340893910 0x8680010634089391 0xfd1cffe7c19f793f 0x7fd1cffe7c19f793

def z1426 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0xfffc0fe03f80ff0f 0xffffc0fe03f80ff0

def z1427 : W := mkw 0x81ffffdee726000f 0xe81ffffdee726000 0xfdffffffc79f0007 0x7fdffffffc79f000

def z1428 : W := mkw 0x80dfe108b776000d 0x380dfe108b776000 0x7cfff018ffff0007 0xe7cfff018ffff000

def z1429 : W := mkw 0x0042800010500000 0x1004280001050000 0x10e4b000399b0001 0x010e4b000399b000

def z1430 : W := mkw 0x00f69ed640000002 0x800f69ed64000000 0xfdffffffc0000000 0x3fdffffffc000000

def z1431 : W := mkw 0x11201fdec0000263 0xc11201fdec000026 0x81000fffc0000e30 0x381000fffc0000e3

def z1432 : W := mkw 0x80d6a00035520004 0x380d6a0003552000 0x1ce4b000399b0001 0xc1ce4b000399b000

def z1433 : W := mkw 0x0042905640000000 0x8004290564000000 0xf407f4ffc0000000 0x3f407f4ffc000000

def z1434 : W := mkw 0x11ffffdec000026f 0xc11ffffdec000026 0xffffffffc6008ffa 0xfffffffffc6008ff

def z1435 : W := mkw 0x90dfe0003776026c 0x390dfe0003776026 0xfffffb003fff8fff 0xdfffffb003fff8ff

def z1436 : W := mkw 0x6800106340893910 0x8680010634089391 0xf604fcffc19ff9ff 0x7f604fcffc19ff9f

def z1437 : W := mkw 0x680000212d89fd10 0x2680000212d89fd1 0x00000000399f793f 0x400000000399f793

def z1438 : W := mkw 0x106bdd5ec2240269 0x8106bdd5ec224026 0xffffffffc6648ffe 0xfffffffffc6648ff

def z1439 : W := mkw 0x00f68e9400000002 0x000f68e940000000 0xbdfc8fe700000000 0x1bdfc8fe70000000

def z1440 : W := mkw 0x1009410882240269 0x0100941088224026 0xcf1b0b18c6608ffc 0xfcf1b0b18c6608ff

def z1441 : W := mkw 0x0000104240000000 0x8000010424000000 0xc000f4e7c0000000 0x3c000f4e7c000000

def z1442 : W := mkw 0xe89d602127af391c 0x2e89d602127af391 0x201c7000079f793f 0x4201c7000079f793

def z1443 : W := mkw 0x01ffef9c8000000f 0x401ffef9c8000000 0xfdff8fff00000000 0x3fdff8fff0000000

def z1444 : W := mkw 0x00dff0424224000c 0x800dff0424224000 0xfcfff4e7c664093e 0xffcfff4e7c664093

def z1445 : W := mkw 0x6809402102ad3918 0x06809402102ad391 0x6c1b400007ff793f 0xc6c1b400007ff793

def z1446 : W := mkw 0x01ffffded850c08f 0xd01ffffded850c08 0xfffffffff860f0c9 0xffffffffff860f0c

def z1447 : W := mkw 0x01f6bed640000006 0xc01f6bed64000000 0xfdffbfff00000000 0x3fdffbfff0000000

def z1448 : W := mkw 0x80d6a00037760004 0x380d6a0003776000 0x74e4f0003fff0007 0xc74e4f0003fff000

def z1449 : W := mkw 0x01ffffdef550000f 0xf01ffffdef550000 0xfdfffffffff80007 0xffdfffffffff8000

def z1450 : W := mkw 0x01629fdec0000003 0xc01629fdec000000 0xfde7ffffc0000000 0x3fde7ffffc000000

def z1451 : W := mkw 0x1009410882240269 0x0100941088224026 0xff1f4b18c7e48fff 0xfff1f4b18c7e48ff

def z1452 : W := mkw 0x8042800037760000 0x3804280003776000 0x7ce7f0003fff0007 0xc7ce7f0003fff000

def z1453 : W := mkw 0x80d6a00035520004 0x380d6a0003552000 0x50e4f000399f0005 0x050e4f000399f000

def z1454 : W := mkw 0x680000213dd9fd90 0x3680000213dd9fd9 0x020000003fffffff 0xc020000003ffffff

def z1455 : W := mkw 0xe8dfe02137ff391c 0x3e8dfe02137ff391 0xfcfff000ffff793f 0xffcfff000ffff793

def z1456 : W := mkw 0x80d6a00035520004 0x380d6a0003552000 0xdee7b81839fb81cd 0xedee7b81839fb81c

def z1457 : W := mkw 0x00b41ec26d00c402 0xa00b41ec26d00c40 0xfffcffe7fe008600 0xbfffcffe7fe00860

def z1458 : W := mkw 0x90dfe108b776026d 0x390dfe108b776026 0x1bffbb183ffb86c1 0x81bffbb183ffb86c

def z1459 : W := mkw 0x680000210889f990 0x0680000210889f99 0x02000000019ff9ff 0x402000000019ff9f

def z1460 : W := mkw 0x009412c240000002 0x8009412c24000000 0xf51cf7e7c0000000 0x3f51cf7e7c000000

def z1461 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0x7efff0003fff8e0f 0xc7efff0003fff8e0

def z1462 : W := mkw 0x1009410882240269 0x0100941088224026 0xfffb4b18fe648fff 0xffffb4b18fe648ff

def z1463 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0xffff0ff83f80fe0b 0xfffff0ff83f80fe0

def z1464 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0xfffffb183fff8fcf 0xffffffb183fff8fc

def z1465 : W := mkw 0x80d6b04275520004 0xb80d6b0427552000 0x10e4b4e7399b0001 0x010e4b4e7399b000

def z1466 : W := mkw 0x01201fdec0000003 0xc01201fdec000000 0xf504ffffc19f0007 0x7f504ffffc19f000

def z1467 : W := mkw 0x20628c151858d180 0x120628c151858d18 0xcae38c1f3878f1cc 0xacae38c1f3878f1c

def z1468 : W := mkw 0x90dfe108b776026d 0x390dfe108b776026 0xfcfff018ffff09ff 0xffcfff018ffff09f

def z1469 : W := mkw 0x016bffdec000000f 0xc016bffdec000000 0xdde3ffffc0000000 0x3dde3ffffc000000

def z1470 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xfdffffffc000010c 0x7fdffffffc000010

def z1471 : W := mkw 0x6800002100893910 0x0680000210089391 0x000000000018793d 0x4000000000018793

def z1472 : W := mkw 0x900961088226026d 0x0900961088226026 0xef1b7b18c6678ffe 0xfef1b7b18c6678ff

def z1473 : W := mkw 0x6800106340893910 0x8680010634089391 0xd404f4e7c19f713d 0x6d404f4e7c19f713

def z1474 : W := mkw 0x78094129afadff79 0x278094129afadff7 0xef1b4b18ffffffff 0xfef1b4b18fffffff

def z1475 : W := mkw 0x40200ea00880ec02 0x040200ea00880ec0 0xbff80fe03e00fe0b 0xdbff80fe03e00fe0

def z1476 : W := mkw 0x01f6bed640000006 0xc01f6bed64000000 0x74e4f4e7019f0007 0x474e4f4e7019f000

def z1477 : W := mkw 0x010013cac0000003 0xc010013cac000000 0xf504f7e7c0000000 0x3f504f7e7c000000

def z1478 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0xfdfffb003fff0007 0xdfdfffb003fff000

def z1479 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xfdffffffc0000938 0x3fdffffffc000093

def z1480 : W := mkw 0x80dfe2803776040e 0x380dfe2803776040 0x7dfff3003fff0607 0xc7dfff3003fff060

def z1481 : W := mkw 0xe80000213ffffd10 0x3e80000213ffffd1 0x020000003fffff3f 0xc020000003fffff3

def z1482 : W := mkw 0x00629c5640000000 0x800629c564000000 0xfee7fcffc06489fe 0xffee7fcffc06489f

def z1483 : W := mkw 0x01201ed640000002 0xc01201ed64000000 0x1004b4e700000000 0x01004b4e70000000

def z1484 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0x10e4f4e7c0000000 0x010e4f4e7c000000

def z1485 : W := mkw 0x81f6bed675520006 0xf81f6bed67552000 0x10e4b4e738000000 0x010e4b4e73800000

def z1486 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xfdffffffc0040832 0x3fdffffffc004083

def z1487 : W := mkw 0x80ffee943776000e 0x380ffee943776000 0xfdffffff3fff0007 0xffdffffff3fff000

def z1488 : W := mkw 0x0000104240000000 0x8000010424000000 0xf404f4e7c0007009 0x7f404f4e7c000700

def z1489 : W := mkw 0xe00000213ffefd80 0x3e00000213ffefd8 0x020000003fffffcf 0xc020000003fffffc

def z1490 : W := mkw 0x01ffffded050008f 0xd01ffffded050008 0xfdffffffc06000c0 0x3fdffffffc06000c

def z1491 : W := mkw 0x11ffffdec224026f 0xc11ffffdec224026 0xffffffffc0648ffc 0x3ffffffffc0648ff

def z1492 : W := mkw 0x809d60003776000c 0x3809d60003776000 0x3cfc70003fff0007 0xc3cfc70003fff000

def z1493 : W := mkw 0x014bf15ec000000d 0xc014bf15ec000000 0xfd1fffffc0000000 0x3fd1fffffc000000

def z1494 : W := mkw 0x11ffffdec224026f 0xc11ffffdec224026 0xffffffffc6608ff8 0xbffffffffc6608ff

def z1495 : W := mkw 0x0000104240000000 0x8000010424000000 0xf404f4e7c0040134 0x3f404f4e7c004013

def z1496 : W := mkw 0x11ffffdec224026f 0xc11ffffdec224026 0xeffb4fffc6648ffe 0xfeffb4fffc6648ff

def z1497 : W := mkw 0x0000114ac0000001 0x80000114ac000000 0x81000fffc0000000 0x381000fffc000000

def z1498 : W := mkw 0x0000104240000000 0x8000010424000000 0xf404f4e7c1800003 0x7f404f4e7c180000

def z1499 : W := mkw 0x81ffffdec226000f 0xc81ffffdec226000 0xfdffffffc0070000 0x3fdffffffc007000

def z1500 : W := mkw 0x20628c151858d180 0x120628c151858d18 0xdee3fc1f387ff1cd 0xedee3fc1f387ff1c

def z1501 : W := mkw 0x114bf15ec224026d 0xc114bf15ec224026 0xf407f4ffc06409fe 0x7f407f4ffc06409f

def z1502 : W := mkw 0x6800002100893910 0x0680000210089391 0xce03081801fff9ff 0xece03081801fff9f

def z1503 : W := mkw 0x0042904240000000 0x8004290424000000 0xfce7f4e7c0000000 0x3fce7f4e7c000000

def z1504 : W := mkw 0x81dff3def776000f 0xf81dff3def776000 0x611ff3ffc7ff0006 0x3611ff3ffc7ff000

def z1505 : W := mkw 0x01629fdec0000003 0xc01629fdec000000 0x91e08fffc0000000 0x391e08fffc000000

def z1506 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0x9bfc0fe03f80fe09 0x99bfc0fe03f80fe0

def z1507 : W := mkw 0x7809412982ad3b79 0x07809412982ad3b7 0x21184300c79f7f3f 0x521184300c79f7f3

def z1508 : W := mkw 0x20628c151858d180 0x120628c151858d18 0x9ee38c1f3878f0c9 0xc9ee38c1f3878f0c

def z1509 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0x99ffbfffc0000000 0x399ffbfffc000000

def z1510 : W := mkw 0x01ffffdec800c00f 0xc01ffffdec800c00 0xffffffffc000f008 0x3ffffffffc000f00

def z1511 : W := mkw 0x81ffffdeff76c40f 0xf81ffffdeff76c40 0xfffffffffe608600 0xbfffffffffe60860

def z1512 : W := mkw 0x01fffed64000000e 0xc01fffed64000000 0x50e7f4e700000000 0x050e7f4e70000000

def z1513 : W := mkw 0x6800106340893910 0x8680010634089391 0x5004f4e7c19f793f 0x65004f4e7c19f793

def z1514 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xfdfffffff8000001 0xffdfffffff800000

def z1515 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0x9ffc0fe03f80f609 0xc9ffc0fe03f80f60

def z1516 : W := mkw 0x010013cac0000003 0xc010013cac000000 0x810007e7c0000000 0x3810007e7c000000

def z1517 : W := mkw 0x6800002100893910 0x0680000210089391 0x7404f000019f7007 0x47404f000019f700

def z1518 : W := mkw 0x00201c424800c000 0x800201c424800c00 0xfee4fce7f800f009 0xffee4fce7f800f00

def z1519 : W := mkw 0x7800012980893b71 0x07800012980893b7 0x83000b18c000fff8 0x383000b18c000fff

def z1520 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xddffbfff00000000 0x2ddffbfff0000000

def z1521 : W := mkw 0x10ffcf9c8224026b 0x010ffcf9c8224026 0xffffcfffc6648ffe 0xfffffcfffc6648ff

def z1522 : W := mkw 0x11ffffdec224026f 0xc11ffffdec224026 0xfdffffffc6040f3e 0x7fdffffffc6040f3

def z1523 : W := mkw 0x1009410882240269 0x0100941088224026 0xaf1b0b18c6608ffa 0xfaf1b0b18c6608ff

def z1524 : W := mkw 0x014bf15ec000000d 0xc014bf15ec000000 0x6007f0ffc0000000 0x36007f0ffc000000

def z1525 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0xbffc4fe0ff84fe3b 0xdbffc4fe0ff84fe3

def z1526 : W := mkw 0x81ffffdef776000f 0xf81ffffdef776000 0x7dffffff3fff0007 0xc7dffffff3fff000

def z1527 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0x7dffffff00000000 0x07dffffff0000000

def z1528 : W := mkw 0x01f6bed650500006 0xd01f6bed65050000 0x10e4b4e738180001 0x010e4b4e73818000

def z1529 : W := mkw 0x01ffffdec800c00f 0xc01ffffdec800c00 0xfffffffff860f1cd 0xffffffffff860f1c

def z1530 : W := mkw 0x20628c151858d180 0x120628c151858d18 0xdee38c1f39fff1cf 0xedee38c1f39fff1c

def z1531 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xb1fcffffc0000000 0x3b1fcffffc000000

def z1532 : W := mkw 0x81fffed67776000e 0xf81fffed67776000 0x18ffb4e73e600000 0x818ffb4e73e60000

def z1533 : W := mkw 0x69201fffc889f993 0xc69201fffc889f99 0x83000fffc000f9f8 0x383000fffc000f9f

def z1534 : W := mkw 0x90dfe108b776026d 0x390dfe108b776026 0x31fcf300ff9f0e33 0x131fcf300ff9f0e3

def z1535 : W := mkw 0x6800002118d9f990 0x16800002118d9f99 0x0200000039fbf1cd 0xc0200000039fbf1c

def z1536 : W := mkw 0x6800106340893910 0x8680010634089391 0xf604f4e7c1fff9ff 0xff604f4e7c1fff9f

def z1537 : W := mkw 0x1009410882240269 0x0100941088224026 0xff1bcb18c67c8fff 0xfff1bcb18c67c8ff

def z1538 : W := mkw 0x00200e9400000002 0x000200e940000000 0x81000fff00000000 0x381000fff0000000

def z1539 : W := mkw 0x01f6bed640000006 0xc01f6bed64000000 0xf4e4f4e7c004093e 0x7f4e4f4e7c004093

def z1540 : W := mkw 0x7809402102ad3b78 0x07809402102ad3b7 0x7e1ff00007ffffff 0xc7e1ff00007fffff

def z1541 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0x10e7b4ff00000000 0x010e7b4ff0000000

def z1542 : W := mkw 0x01fffed64224000e 0xc01fffed64224000 0x7cfff4e706640006 0xc7cfff4e70664000

def z1543 : W := mkw 0x80dfe2803776000e 0x380dfe2803776000 0x7dfff3e03fff0007 0xd7dfff3e03fff000

def z1544 : W := mkw 0x116bffdec224026f 0xc116bffdec224026 0xef1bffffc6648ffe 0xfef1bffffc6648ff

def z1545 : W := mkw 0x019d73cac000000f 0xc019d73cac000000 0xa11c77e7c0000000 0x3a11c77e7c000000

def z1546 : W := mkw 0x01ffffdec800c08f 0xc01ffffdec800c08 0xffffffffc00080c0 0x3ffffffffc00080c

def z1547 : W := mkw 0x814bf15ed276000d 0xd814bf15ed276000 0xf407f4ffc1ff0007 0x7f407f4ffc1ff000

def z1548 : W := mkw 0x7800002102ad3b70 0x07800002102ad3b7 0x0000000001ff79ff 0x40000000001ff79f

def z1549 : W := mkw 0x01ffffdec224000f 0xc01ffffdec224000 0xffffffffc6648e0e 0xfffffffffc6648e0

def z1550 : W := mkw 0x11ffffdeef24c66f 0xe11ffffdeef24c66 0xfffffffffe648ffe 0xffffffffffe648ff

def z1551 : W := mkw 0x0000104240000000 0x8000010424000000 0xff1cffe7c6008e0a 0xfff1cffe7c6008e0

def z1552 : W := mkw 0x11ffffdec224026f 0xc11ffffdec224026 0x50e7f4ffc06401f4 0x250e7f4ffc06401f

def z1553 : W := mkw 0x1009514ac2240269 0x81009514ac224026 0xf407f4ffc06401f4 0x3f407f4ffc06401f

def z1554 : W := mkw 0x90dfe108b776026d 0x390dfe108b776026 0x7dfff3003fff0607 0xc7dfff3003fff060

def z1555 : W := mkw 0x680000212d89fd10 0x2680000212d89fd1 0x020000003f9bfe0b 0xc020000003f9bfe0

def z1556 : W := mkw 0x7800002100893b70 0x07800002100893b7 0x02000000019fffff 0x402000000019ffff

def z1557 : W := mkw 0x00201c4240000000 0x800201c424000000 0xfce4fce7c0000000 0x3fce4fce7c000000

def z1558 : W := mkw 0x1009514ac2240269 0x81009514ac224026 0xf51cf7e7c6040e32 0x3f51cf7e7c6040e3

def z1559 : W := mkw 0x01ffffdec800c00f 0xc01ffffdec800c00 0xfffffffffe00fe0b 0xffffffffffe00fe0

def z1560 : W := mkw 0x01b41fdec0000003 0xc01b41fdec000000 0xfdfcffffc0000000 0x3fdfcffffc000000

def z1561 : W := mkw 0x80dfe0003552000c 0x380dfe0003552000 0x7cfff000399f0007 0x47cfff000399f000

def z1562 : W := mkw 0x0100115ec0000001 0xc0100115ec000000 0xf404f4ffc0000000 0x3f404f4ffc000000

def z1563 : W := mkw 0x80d6a00037760004 0x380d6a0003776000 0x3cfcb0003fff0007 0xc3cfcb0003fff000

def z1564 : W := mkw 0x01201fdec0000003 0xc01201fdec000000 0xb5040fffc0000000 0x3b5040fffc000000

def z1565 : W := mkw 0x0800104240010010 0x8080010424001001 0xf404f4e7c0070030 0x3f404f4e7c007003

def z1566 : W := mkw 0x20628c151858d180 0x120628c151858d18 0x10e3841f387870c1 0x010e3841f387870c

def z1567 : W := mkw 0x6800002100893910 0x0680000210089391 0x1004b000019b7001 0x01004b000019b700

def z1568 : W := mkw 0x11ffffdec000026f 0xc11ffffdec000026 0xffffffffc0608ffc 0xfffffffffc0608ff

def z1569 : W := mkw 0x11201fdec2240263 0xc11201fdec224026 0x83000fffc6648ffe 0xf83000fffc6648ff

def z1570 : W := mkw 0x90dfe108b776026d 0x390dfe108b776026 0x7ffff300ffff8fff 0xd7ffff300ffff8ff

def z1571 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xf4e7f4ffc0000000 0x3f4e7f4ffc000000

def z1572 : W := mkw 0x90dfe108b776026d 0x390dfe108b776026 0xfefff818ffff81ff 0xefefff818ffff81f

def z1573 : W := mkw 0x11bd7fdec224026f 0xc11bd7fdec224026 0xef1f7fffc6648ffe 0xfef1f7fffc6648ff

def z1574 : W := mkw 0x60f68eb53dd8fd82 0x360f68eb53dd8fd8 0x0bfb0b183ff8ffcf 0xc0bfb0b183ff8ffc

def z1575 : W := mkw 0x40200c200880e800 0x040200c200880e80 0xbffc0fe03f80fe0b 0xdbffc0fe03f80fe0

def z1576 : W := mkw 0x0000104240000000 0x8000010424000000 0xf404f4e7c01f0004 0x3f404f4e7c01f000

def z1577 : W := mkw 0x0009504242240008 0x8000950424224000 0xfc1ff4e7c6640006 0xffc1ff4e7c664000

def z1578 : W := mkw 0x01ffffded850c08f 0xd01ffffded850c08 0xfffffffff86081cc 0xffffffffff86081c

def z1579 : W := mkw 0x01629fdec0000003 0xc01629fdec000000 0x89e30fffc0000000 0x389e30fffc000000

def z1580 : W := mkw 0x11ffffdec224026f 0xc11ffffdec224026 0xfdffffffc66401f6 0xffdffffffc66401f

def z1581 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0x71fff7ffc0000000 0x371fff7ffc000000

def z1582 : W := mkw 0xe8dfe02137ff391c 0x3e8dfe02137ff391 0x08fb00003fff793f 0xc08fb00003fff793

def z1583 : W := mkw 0x20628c151858d180 0x120628c151858d18 0x5ce3841f387871c5 0xe5ce3841f387871c

def z1584 : W := mkw 0x20628c151858d180 0x120628c151858d18 0x5ae38c1f3878f1c5 0xa5ae38c1f3878f1c

def z1585 : W := mkw 0x78295d7fcaadfbf9 0x878295d7fcaadfbf 0xef1b4fffc664fffe 0xfef1b4fffc664fff

def z1586 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0x7cfff0183fff01c7 0xe7cfff0183fff01c

def z1587 : W := mkw 0x0000000000000000 0x0000000000000000 0x7ce4f000399f0007 0xc7ce4f000399f000

def z1588 : W := mkw 0x6800106340893910 0x8680010634089391 0xf704ffe7c19fff3f 0x7f704ffe7c19fff3

def z1589 : W := mkw 0x6800106340893910 0x8680010634089391 0xfce4f4e7f99f793f 0xffce4f4e7f99f793

def z1590 : W := mkw 0x81ffffdeff76c00f 0xf81ffffdeff76c00 0xfffffffffffff00f 0xffffffffffffff00

def z1591 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0x58fff0003fff0005 0x858fff0003fff000

def z1592 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0xbffc0fe0ff80ff3b 0xfbffc0fe0ff80ff3

def z1593 : W := mkw 0x11ffffdec224026f 0xc11ffffdec224026 0xffffffffc6048e3a 0xfffffffffc6048e3

def z1594 : W := mkw 0x20628c151858d180 0x120628c151858d18 0x9ee30c1f3860f1c9 0xe9ee30c1f3860f1c

def z1595 : W := mkw 0x01ffffdec224000f 0xc01ffffdec224000 0xfdffffffc6600000 0xbfdffffffc660000

def z1596 : W := mkw 0x80dfe0003552000c 0x380dfe0003552000 0x7cfff0003f9b0003 0xc7cfff0003f9b000

def z1597 : W := mkw 0x01b41fdeed00c403 0xe01b41fdeed00c40 0x8bf80ffffe008600 0xb8bf80ffffe00860

def z1598 : W := mkw 0x01f6bed640000006 0xc01f6bed64000000 0x31fcb7e700000000 0x131fcb7e70000000

def z1599 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xffffffffc6048f3e 0xfffffffffc6048f3

def z1600 : W := mkw 0x689400212d89fd10 0x2689400212d89fd1 0x7efcf0003f9fff3f 0xc7efcf0003f9fff3

def z1601 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xfdffffffc6000e02 0x3fdffffffc6000e0

def z1602 : W := mkw 0x01f6bed640000006 0xc01f6bed64000000 0x10e4b4e7019b0001 0x010e4b4e7019b000

def z1603 : W := mkw 0x009d400027240008 0x2009d40002724000 0x7cfff0003fff0007 0xc7cfff0003fff000

def z1604 : W := mkw 0x01b41fdec0000003 0xc01b41fdec000000 0x91e40fffc0000000 0x391e40fffc000000

def z1605 : W := mkw 0x80d6a00035520004 0x380d6a0003552000 0x18fcb0003f9b0001 0x818fcb0003f9b000

def z1606 : W := mkw 0x0100115ec0000001 0xc0100115ec000000 0x800004ffc0000000 0x3800004ffc000000

def z1607 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0x9ff80fe03e00fe09 0xd9ff80fe03e00fe0

def z1608 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0x39ffffffc0000000 0x139ffffffc000000

def z1609 : W := mkw 0x01ffffdeed00c40f 0xe01ffffdeed00c40 0xfffffffffe008e0a 0xffffffffffe008e0

def z1610 : W := mkw 0x68201c634889f910 0x868201c634889f91 0x82000ce7c000f938 0x382000ce7c000f93

def z1611 : W := mkw 0x01f6bfdec0000007 0xc01f6bfdec000000 0x11e4bfff00000000 0x011e4bfff0000000

def z1612 : W := mkw 0x6800002100893910 0x0680000210089391 0x000000000187793a 0x0000000000187793

def z1613 : W := mkw 0x780000211afdfbf0 0x1780000211afdfbf 0x020000003fffffff 0xc020000003ffffff

def z1614 : W := mkw 0x01f6bed64800c006 0xc01f6bed64800c00 0x10e4b4e738007001 0x010e4b4e73800700

def z1615 : W := mkw 0x81fffed67776000e 0xf81fffed67776000 0xfcfffcff3fff0007 0xefcfffcff3fff000

def z1616 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0xa9ff7fffc0000000 0x3a9ff7fffc000000

def z1617 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0xfffc8fe03f98fe0f 0xdfffc8fe03f98fe0

def z1618 : W := mkw 0x10bd5fcac224026b 0x810bd5fcac224026 0xffffffffc6648ffe 0xfffffffffc6648ff

def z1619 : W := mkw 0x81f6bed677760006 0xf81f6bed67776000 0x10e4b4e73fff0007 0xc10e4b4e73fff000

def z1620 : W := mkw 0x0094104240000000 0x8009410424000000 0xfcfcf4e7c0000000 0x3fcfcf4e7c000000

def z1621 : W := mkw 0x01ffffdec000000f 0xc01ffffdec000000 0x69fffbffc0000000 0x369fffbffc000000

def z1622 : W := mkw 0x91ffffdee726026f 0xe91ffffdee726026 0xffffffffc7e78ffe 0xfffffffffc7e78ff

def z1623 : W := mkw 0x80dfe0003776000c 0x380dfe0003776000 0x7cfff00039ff0005 0x07cfff00039ff000

def z1624 : W := mkw 0x0000104240000000 0x8000010424000000 0xb40404e7c0000000 0x3b40404e7c000000

def z1625 : W := mkw 0x1009514ac2240269 0x81009514ac224026 0xff1fffffc7ff8fff 0xfff1fffffc7ff8ff

def z1626 : W := mkw 0x20200c010808d100 0x020200c010808d10 0xdee38c1f3878f1cd 0xedee38c1f3878f1c

def z1627 : W := mkw 0x80dfe108b776000d 0x380dfe108b776000 0x7dfff300ffff0007 0xd7dfff300ffff000

def z1628 : W := mkw 0x01ffffdec224000f 0xc01ffffdec224000 0xffffffffc66481ce 0xfffffffffc66481c

def z1629 : W := mkw 0x80dff0427776000c 0xb80dff0427776000 0xfcfff4e7ffff093f 0xffcfff4e7ffff093

def z1630 : W := mkw 0x6800106340893910 0x8680010634089391 0xf404f4e7c19f7833 0x3f404f4e7c19f783

def z1631 : W := mkw 0x80d6a00035520004 0x380d6a0003552000 0x3cfcb000399b0001 0x03cfcb000399b000

def z1632 : W := mkw 0x81ffffdef776000f 0xf81ffffdef776000 0xfdffffffffe00003 0xffdffffffffe0000

def z1633 : W := mkw 0x90dfe108b776026d 0x390dfe108b776026 0xfdfffb18ffff0e37 0xffdfffb18ffff0e3

def z1634 : W := mkw 0x0000104240000000 0x8000010424000000 0xf404f4e7c0040006 0x7f404f4e7c004000

def z1635 : W := mkw 0xe800002137ff3910 0x3e800002137ff391 0x000000003fff7007 0xc000000003fff700

def z1636 : W := mkw 0x78295febcaadff7b 0x878295febcaadff7 0xef1b4fffc664fffe 0xfef1b4fffc664fff

def z1637 : W := mkw 0x40b40ea02d80ec02 0x240b40ea02d80ec0 0x3bfc0fe03f80fe03 0x93bfc0fe03f80fe0

def z1638 : W := mkw 0x01dff3dec000000f 0xc01dff3dec000000 0x4007f0ffc0000000 0x24007f0ffc000000

def z1639 : W := mkw 0x780941299afdfbf9 0x1780941299afdfbf 0xef1b4b18ffffffff 0xfef1b4b18fffffff

def z1640 : W := mkw 0x6800002100893910 0x0680000210089391 0xaf180b00079fff3f 0xdaf180b00079fff3

def z1641 : W := mkw 0x11ffffdec224026f 0xc11ffffdec224026 0xfdffffffc06000c0 0x3fdffffffc06000c

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(1,[z0,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z7,z5]),(0,[z8,z6,z1,z2,z3,z4,z9]),(0,[z6,z1,z2,z10,z3,z11,z5])],[(0,[z12,z6,z1,z2,z3,z13,z5]),(0,[z14,z1,z2,z3,z4,z5,z15]),(0,[z6,z1,z2,z3,z4,z5,z16]),(0,[z6,z1,z2,z4,z17,z5,z18])],[(0,[z12,z19,z1,z2,z3,z4,z5]),(0,[z20,z6,z1,z2,z3,z4,z5]),(0,[z6,z21,z1,z2,z3,z4,z5])],[(0,[z22,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z23,z3,z4,z5]),(0,[z24,z1,z2,z3,z25,z4,z5]),(0,[z26,z1,z2,z27,z3,z4,z5]),(0,[z8,z6,z28,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z29]),(0,[z30,z6,z1,z2,z3,z4,z5])],[(0,[z26,z1,z2,z3,z4,z5,z15]),(0,[z6,z1,z2,z31,z3,z4,z5]),(0,[z6,z1,z32,z2,z3,z4,z5]),(0,[z33,z6,z1,z2,z3,z4,z5]),(1,[z1,z34,z2,z3,z4,z5])],[(0,[z35,z26,z1,z2,z3,z4,z5]),(0,[z36,z6,z1,z2,z3,z4,z5]),(0,[z37,z6,z1,z2,z3,z4,z38]),(0,[z39,z6,z1,z3,z4,z5,z40])],[(0,[z41,z26,z1,z2,z3,z4,z5])],[(0,[z1,z42,z2,z43,z3,z4,z5]),(0,[z1,z42,z2,z44,z3,z4,z5]),(0,[z45,z1,z2,z3,z46,z4,z5]),(0,[z6,z1,z2,z3,z47,z4,z5])],[(1,[z1,z2,z3,z4,z5,z48]),(0,[z1,z2,z3,z4,z49,z5,z15]),(0,[z26,z1,z2,z50,z3,z4,z5]),(0,[z26,z1,z2,z10,z3,z4,z5]),(1,[z6,z1,z2,z3,z4,z51]),(0,[z6,z1,z52,z53,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z54,z5])],[(0,[z6,z1,z42,z2,z3,z4,z38]),(0,[z45,z1,z2,z55,z3,z4,z5]),(0,[z56,z26,z1,z2,z3,z4,z5])],[(0,[z6,z1,z2,z3,z57,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z58]),(0,[z26,z1,z59,z2,z3,z4,z5]),(0,[z60,z6,z1,z2,z3,z4,z5])],[(0,[z6,z1,z2,z3,z61,z4,z5]),(0,[z6,z1,z62,z2,z3,z4,z5])],[(0,[z6,z1,z2,z3,z4,z63,z5]),(0,[z64,z12,z1,z2,z3,z4,z5]),(0,[z1,z2,z65,z3,z25,z4,z5]),(0,[z6,z1,z2,z65,z3,z4,z66]),(0,[z6,z1,z2,z3,z4,z67,z5])],[(1,[z6,z1,z2,z3,z4,z66])],[(0,[z12,z14,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z68,z4,z69,z5])],[(0,[z45,z1,z2,z3,z4,z17,z5]),(0,[z26,z1,z2,z3,z4,z66,z5]),(0,[z6,z70,z1,z2,z3,z4,z5])]],
   [[(0,[z45,z1,z2,z71,z3,z4,z5]),(0,[z6,z1,z2,z72,z3,z4,z5])],[(0,[z73,z6,z1,z2,z3,z4,z5]),(0,[z74,z6,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z15,z75]),(1,[z76,z1,z2,z3,z4,z5])],[(0,[z1,z77,z2,z3,z25,z4,z5]),(0,[z1,z2,z3,z4,z5,z15,z78])],[(0,[z12,z79,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z15,z38]),(0,[z80,z6,z1,z55,z3,z4,z5]),(0,[z81,z6,z1,z2,z3,z4,z5])],[(0,[z6,z1,z2,z3,z4,z82,z5]),(0,[z83,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z84]),(0,[z6,z1,z2,z3,z85,z4,z5]),(0,[z86,z87,z1,z2,z3,z4,z5])],[(0,[z45,z1,z1,z2,z3,z4,z5]),(0,[z1,z88,z2,z3,z25,z4,z5]),(0,[z6,z1,z52,z2,z3,z4,z5])],[(0,[z89,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z90,z2,z3,z4,z5])],[(0,[z6,z1,z2,z3,z91,z4,z5]),(0,[z92,z1,z2,z3,z4,z5,z15]),(0,[z12,z1,z2,z3,z93,z4,z5]),(0,[z6,z1,z2,z53,z3,z4,z38])],[(1,[z26,z1,z2,z3,z4,z94])],[(0,[z95,z1,z42,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z96,z5,z15]),(0,[z6,z1,z2,z3,z4,z38,z97]),(1,[z98,z1,z2,z3,z4,z5])],[(0,[z6,z1,z99,z2,z3,z4,z5])],[(1,[z56,z6,z1,z2,z10,z5])],[(0,[z1,z2,z3,z4,z5,z100,z15]),(0,[z6,z1,z2,z3,z4,z101,z5]),(0,[z6,z1,z102,z2,z3,z4,z5]),(0,[z41,z6,z1,z2,z3,z4,z17]),(0,[z6,z1,z2,z3,z103,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z104])],[(0,[z45,z1,z77,z2,z3,z4,z5]),(0,[z105,z12,z1,z2,z3,z4,z5]),(0,[z0,z6,z1,z2,z3,z4,z5]),(1,[z106,z6,z1,z2,z3,z4])],[(0,[z6,z1,z2,z3,z107,z4,z5]),(1,[z6,z1,z2,z3,z4,z108]),(1,[z6,z1,z2,z3,z4,z109])],[(0,[z110,z6,z1,z2,z3,z4,z5]),(0,[z6,z2,z111,z3,z68,z4,z5]),(0,[z0,z112,z1,z2,z3,z4,z5]),(0,[z113,z6,z1,z2,z3,z4,z5]),(0,[z39,z6,z1,z3,z114,z4,z5]),(0,[z6,z1,z2,z3,z115,z4,z5])]],
   [[(0,[z1,z2,z3,z25,z4,z116,z5]),(0,[z6,z1,z2,z117,z3,z4,z5])],[(0,[z1,z2,z118,z3,z25,z4,z5]),(0,[z12,z1,z2,z3,z4,z119,z5]),(1,[z6,z1,z2,z3,z120,z5]),(0,[z6,z1,z2,z3,z4,z121,z5]),(0,[z6,z1,z2,z3,z4,z5,z122])],[(0,[z12,z1,z2,z3,z4,z4,z5]),(0,[z123,z6,z1,z2,z3,z4,z5]),(0,[z1,z2,z10,z3,z4,z5,z15]),(1,[z6,z1,z2,z3,z4,z82])],[(0,[z6,z1,z2,z3,z4,z124,z5]),(1,[z6,z1,z125,z3,z4,z5]),(0,[z6,z1,z2,z3,z93,z4,z122]),(0,[z126,z6,z1,z2,z3,z4,z5])],[(0,[z127,z45,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z5,z15]),(0,[z128,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z69,z49,z5]),(0,[z129,z130,z1,z2,z3,z4,z5]),(1,[z131,z1,z2,z3,z4,z5])],[(0,[z6,z1,z2,z3,z4,z132,z5]),(0,[z133,z6,z1,z2,z3,z4,z5]),(0,[z134,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z135])],[(0,[z12,z127,z1,z2,z3,z4,z5]),(0,[z136,z6,z1,z2,z3,z4,z5]),(0,[z8,z26,z1,z2,z3,z4,z5])],[(0,[z6,z1,z2,z3,z137,z4,z5]),(0,[z12,z1,z2,z3,z4,z5,z18]),(0,[z138,z1,z2,z3,z4,z5,z15]),(0,[z80,z6,z14,z2,z3,z4,z5]),(0,[z6,z2,z3,z11,z4,z49,z5])],[(0,[z6,z1,z139,z2,z3,z4,z5]),(0,[z6,z1,z2,z140,z3,z4,z5])],[(0,[z141,z1,z2,z3,z25,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z142]),(0,[z6,z1,z2,z3,z4,z143,z5]),(0,[z6,z1,z2,z3,z4,z96,z38]),(0,[z6,z1,z144,z2,z3,z4,z5])],[(0,[z45,z6,z1,z2,z3,z4,z5]),(0,[z26,z6,z1,z2,z3,z4,z66]),(0,[z6,z1,z2,z3,z4,z145,z5]),(1,[z6,z1,z146,z3,z4,z5])],[(0,[z147,z1,z42,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z148,z5]),(0,[z6,z1,z2,z3,z4,z5,z149]),(0,[z12,z129,z1,z2,z3,z4,z5]),(0,[z6,z28,z1,z2,z3,z11,z5])],[(0,[z1,z42,z2,z3,z4,z119,z5]),(0,[z45,z112,z1,z2,z3,z4,z5]),(0,[z6,z1,z150,z2,z3,z4,z5]),(0,[z1,z2,z3,z25,z4,z94,z5]),(0,[z6,z1,z2,z3,z4,z5,z151]),(0,[z26,z1,z2,z3,z4,z5,z40]),(1,[z6,z28,z2,z3,z11,z5]),(0,[z6,z1,z2,z65,z4,z17,z5])],[(0,[z6,z152,z1,z2,z3,z4,z5]),(1,[z1,z2,z3,z153,z4,z5])],[(0,[z154,z6,z1,z2,z3,z4,z5]),(0,[z155,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z156,z5])],[(0,[z1,z2,z3,z25,z25,z4,z5]),(1,[z1,z2,z3,z157,z4,z5])]],
   [[(0,[z19,z6,z1,z2,z3,z4,z38]),(1,[z1,z59,z2,z3,z4,z5]),(1,[z6,z1,z2,z3,z4,z158])],[(0,[z26,z159,z1,z2,z3,z4,z5]),(0,[z6,z160,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z161,z4,z5])],[(0,[z1,z42,z2,z3,z4,z5,z18]),(0,[z6,z1,z162,z2,z3,z4,z5])],[(0,[z26,z1,z2,z3,z4,z49,z5]),(0,[z26,z28,z1,z2,z3,z4,z5])],[(0,[z6,z1,z2,z55,z3,z4,z5]),(0,[z163,z6,z1,z2,z3,z4,z5]),(0,[z141,z6,z2,z3,z68,z4,z5]),(0,[z6,z1,z2,z3,z4,z116,z66]),(0,[z147,z6,z164,z2,z3,z4,z5])],[],[(0,[z37,z45,z1,z2,z3,z4,z5]),(0,[z74,z6,z1,z2,z3,z25,z5])],[(0,[z6,z165,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z166,z3,z4,z5]),(0,[z6,z14,z1,z2,z3,z4,z167]),(0,[z147,z6,z1,z99,z2,z3,z4]),(0,[z6,z1,z2,z3,z4,z5,z168])],[(0,[z6,z169,z1,z2,z3,z4,z5]),(1,[z1,z2,z3,z170,z4,z5]),(0,[z6,z1,z99,z3,z4,z119,z5])],[(0,[z45,z1,z2,z3,z4,z5,z122]),(0,[z6,z1,z2,z3,z68,z4,z66]),(0,[z6,z171,z1,z2,z3,z4,z5])],[(0,[z6,z1,z172,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z17,z5])],[(0,[z6,z1,z2,z71,z3,z4,z5]),(0,[z6,z1,z2,z3,z173,z4,z5]),(1,[z126,z1,z2,z3,z4,z5])],[(0,[z174,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z175,z5]),(0,[z6,z1,z2,z111,z3,z4,z66])],[(0,[z6,z1,z2,z3,z4,z176,z5]),(0,[z80,z177,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z178,z4,z5]),(0,[z141,z6,z1,z2,z3,z4,z179])],[(0,[z6,z1,z2,z3,z4,z5,z167]),(0,[z6,z1,z2,z3,z114,z11,z5])],[(0,[z26,z1,z2,z3,z180,z4,z5]),(0,[z6,z1,z2,z3,z119,z49,z5]),(0,[z6,z1,z2,z3,z4,z181,z5])]],
   [[(0,[z6,z1,z1,z2,z3,z4,z5]),(0,[z1,z2,z111,z3,z4,z5,z15]),(0,[z6,z1,z2,z3,z4,z94,z66]),(0,[z8,z6,z1,z2,z3,z4,z182]),(0,[z6,z1,z2,z3,z11,z4,z66])],[(0,[z1,z42,z2,z65,z3,z4,z5]),(0,[z183,z6,z1,z2,z3,z4,z5]),(0,[z73,z6,z1,z2,z46,z4,z5]),(0,[z184,z6,z1,z2,z3,z4,z5]),(0,[z185,z6,z1,z2,z3,z4,z5]),(0,[z186,z6,z1,z2,z3,z4,z5])],[(1,[z1,z2,z3,z187,z4,z5]),(0,[z112,z1,z2,z3,z4,z5,z15]),(0,[z6,z1,z2,z3,z188,z4,z5])],[(0,[z45,z6,z92,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z25,z4,z66]),(0,[z6,z1,z2,z189,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z190,z5]),(1,[z191,z1,z2,z3,z4,z5]),(0,[z6,z1,z192,z2,z3,z4,z5]),(1,[z6,z164,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z193])],[(0,[z6,z1,z2,z3,z194,z4,z5]),(0,[z6,z1,z195,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z196])],[(0,[z1,z2,z3,z4,z5,z15,z197])],[(0,[z73,z1,z2,z3,z4,z5,z15]),(0,[z74,z1,z2,z3,z4,z5,z15]),(0,[z26,z1,z2,z3,z114,z4,z5]),(0,[z80,z6,z1,z2,z3,z4,z38])],[(0,[z6,z1,z2,z3,z4,z198,z5]),(0,[z199,z26,z1,z2,z3,z4,z5]),(0,[z6,z1,z200,z2,z3,z4,z5]),(0,[z6,z1,z2,z201,z3,z4,z5])],[(1,[z202,z1,z2,z3,z4,z5]),(0,[z26,z1,z2,z118,z3,z4,z5]),(1,[z73,z1,z2,z44,z4,z5]),(0,[z147,z26,z1,z2,z3,z4,z5]),(0,[z6,z1,z77,z2,z3,z4,z5]),(0,[z6,z1,z203,z2,z3,z4,z5])],[(0,[z204,z6,z1,z2,z3,z4,z5]),(0,[z35,z6,z1,z2,z3,z4,z38]),(0,[z12,z6,z1,z2,z3,z4,z38]),(0,[z6,z1,z2,z3,z205,z4,z5])],[(0,[z202,z45,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z46,z4,z66]),(0,[z41,z6,z1,z2,z3,z4,z38]),(0,[z39,z6,z1,z2,z3,z119,z5])],[(0,[z6,z206,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z207]),(0,[z39,z6,z1,z2,z3,z4,z5])],[(0,[z12,z41,z1,z2,z3,z4,z5]),(0,[z208,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z209,z2,z3,z4,z38])],[],[],[(0,[z6,z1,z2,z3,z4,z5,z182])]],
   [[(0,[z147,z12,z1,z2,z3,z4,z5]),(0,[z210,z6,z1,z2,z3,z4,z5])],[(0,[z35,z1,z88,z2,z3,z4,z5]),(0,[z12,z1,z88,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z38,z18])],[(0,[z19,z6,z1,z2,z3,z4,z211]),(0,[z1,z1,z42,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z212,z5]),(0,[z213,z26,z1,z2,z3,z4,z5]),(0,[z6,z28,z1,z2,z3,z4,z214]),(0,[z6,z1,z2,z3,z4,z215,z5]),(0,[z6,z1,z2,z3,z4,z216,z5])],[(1,[z1,z2,z3,z4,z5,z217])],[(0,[z19,z1,z2,z3,z25,z4,z5]),(0,[z14,z1,z42,z2,z3,z4,z5])],[(0,[z6,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z218,z2,z3,z4,z5]),(0,[z1,z2,z53,z3,z25,z4,z5]),(0,[z26,z1,z2,z3,z170,z4,z5])],[(0,[z45,z1,z2,z3,z4,z13,z5]),(0,[z39,z6,z1,z77,z3,z4,z5]),(0,[z219,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z220,z3,z4,z38]),(0,[z6,z1,z2,z3,z221,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z222])],[(0,[z26,z1,z42,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z223,z4,z5]),(0,[z26,z1,z209,z2,z3,z4,z5]),(0,[z6,z112,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z65,z3,z93,z4])],[(0,[z1,z42,z2,z224,z3,z4,z5]),(0,[z6,z1,z209,z2,z3,z114,z5])],[(0,[z6,z1,z2,z225,z3,z4,z5]),(0,[z128,z1,z2,z3,z4,z5,z15])],[(0,[z127,z1,z2,z3,z25,z4,z5]),(0,[z1,z2,z3,z153,z25,z4,z5]),(0,[z8,z6,z1,z2,z3,z49,z5]),(0,[z226,z6,z1,z2,z3,z4,z5]),(0,[z6,z227,z1,z2,z3,z4,z5])],[],[(0,[z1,z42,z88,z2,z3,z4,z5]),(0,[z6,z112,z1,z2,z3,z4,z7])],[(0,[z228,z6,z1,z2,z3,z4,z5]),(0,[z86,z229,z1,z2,z3,z4,z5])],[(0,[z6,z1,z2,z3,z4,z230,z5]),(0,[z12,z1,z2,z3,z4,z116,z5]),(0,[z6,z28,z2,z3,z11,z4,z5])],[(0,[z45,z1,z2,z3,z4,z5,z15]),(0,[z6,z231,z1,z2,z3,z4,z5])]],
   [[(0,[z1,z2,z3,z46,z4,z5,z15]),(0,[z6,z1,z2,z44,z3,z4,z38]),(0,[z39,z232,z1,z2,z3,z4,z5]),(0,[z41,z233,z1,z2,z3,z4,z5])],[(0,[z19,z45,z1,z2,z3,z4,z5]),(0,[z127,z1,z2,z3,z46,z4,z5]),(1,[z234,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z235,z49,z5]),(0,[z6,z1,z236,z2,z3,z4,z5]),(0,[z6,z237,z1,z2,z3,z4,z5])],[(0,[z6,z1,z238,z2,z3,z4,z5]),(0,[z6,z239,z1,z2,z3,z4,z5]),(0,[z240,z6,z1,z2,z3,z4,z38]),(0,[z6,z1,z2,z241,z3,z4,z5])],[(0,[z45,z1,z2,z50,z3,z4,z5]),(0,[z45,z1,z2,z10,z3,z4,z5])],[(0,[z6,z1,z2,z3,z4,z242,z5]),(0,[z243,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z34,z2,z3,z4,z5])],[(0,[z12,z92,z1,z2,z3,z4,z5]),(0,[z26,z1,z2,z53,z3,z4,z5]),(0,[z244,z6,z1,z2,z3,z4,z5])],[(0,[z6,z1,z2,z245,z3,z4,z5]),(0,[z6,z1,z77,z3,z4,z119,z5]),(0,[z6,z1,z2,z3,z4,z66,z246])],[(0,[z79,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z247,z4,z5]),(0,[z6,z1,z2,z3,z248,z4,z5]),(0,[z6,z1,z2,z3,z249,z4,z5])],[(0,[z6,z1,z2,z3,z4,z5,z48]),(0,[z1,z2,z3,z25,z4,z5,z122]),(0,[z24,z250,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z251,z3,z4,z5])],[(0,[z1,z42,z2,z3,z4,z116,z5]),(0,[z1,z2,z3,z114,z25,z4,z5])],[(0,[z92,z1,z42,z2,z3,z4,z5]),(0,[z45,z1,z2,z3,z4,z66,z5]),(0,[z252,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z253,z3,z4,z5]),(0,[z12,z1,z2,z3,z4,z94,z5]),(0,[z6,z1,z55,z3,z221,z4,z5]),(0,[z8,z6,z1,z2,z3,z4,z38]),(0,[z6,z1,z2,z254,z3,z4,z5]),(0,[z6,z1,z2,z65,z4,z69,z5]),(0,[z147,z6,z1,z2,z3,z5,z122])],[(0,[z1,z2,z118,z3,z46,z4,z5]),(0,[z6,z1,z255,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z96,z5,z122])],[(0,[z256,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z257,z5]),(0,[z73,z6,z1,z2,z3,z4,z66]),(0,[z74,z6,z1,z2,z3,z4,z66]),(0,[z37,z1,z2,z3,z25,z4,z5]),(0,[z6,z1,z258,z2,z3,z4,z5]),(0,[z259,z6,z1,z2,z3,z4,z5]),(0,[z260,z6,z1,z2,z3,z4,z5]),(0,[z147,z41,z6,z1,z2,z3,z4])],[(0,[z147,z6,z261,z2,z3,z4,z5])],[(0,[z45,z1,z2,z3,z221,z4,z5])],[(0,[z12,z74,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z25,z11,z4,z5])]],
   [[(0,[z24,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z52,z2,z3,z4,z66])],[(0,[z6,z1,z2,z3,z262,z4,z5]),(0,[z6,z1,z2,z263,z3,z4,z5])],[(0,[z6,z1,z2,z3,z264,z4,z5]),(0,[z6,z1,z265,z2,z3,z4,z5])],[(1,[z6,z1,z2,z178,z4,z5])],[(1,[z6,z1,z2,z3,z4,z9]),(0,[z6,z1,z2,z3,z4,z266,z5]),(0,[z6,z1,z2,z3,z267,z4,z5])],[(0,[z1,z42,z2,z3,z4,z94,z5]),(0,[z268,z14,z1,z2,z3,z4,z5]),(0,[z269,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z99,z2,z3,z4,z66])],[(0,[z6,z112,z1,z2,z68,z4,z5]),(0,[z6,z1,z2,z3,z4,z49,z5]),(0,[z6,z1,z2,z3,z4,z270,z5])],[(0,[z80,z45,z1,z2,z3,z4,z5]),(0,[z12,z199,z1,z2,z3,z4,z5]),(0,[z26,z1,z2,z3,z4,z96,z5]),(0,[z6,z1,z2,z3,z4,z5,z271]),(0,[z147,z6,z1,z2,z3,z4,z122])],[(0,[z1,z42,z2,z3,z25,z4,z5]),(0,[z12,z1,z2,z3,z272,z4,z5]),(0,[z6,z1,z2,z3,z4,z69,z5]),(0,[z6,z1,z2,z3,z273,z4,z5])],[(0,[z12,z1,z2,z65,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z38])],[(0,[z35,z45,z1,z2,z3,z4,z5]),(0,[z12,z45,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z274,z3,z4,z5]),(0,[z147,z6,z1,z2,z275,z4,z5])],[(0,[z41,z45,z1,z2,z3,z4,z5]),(0,[z129,z6,z1,z2,z3,z4,z38]),(0,[z6,z1,z2,z3,z93,z4,z38]),(0,[z129,z6,z1,z52,z3,z4,z5])],[(0,[z1,z2,z3,z4,z17,z5,z15]),(0,[z6,z276,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z277,z4,z5]),(0,[z6,z278,z1,z2,z3,z4,z5]),(1,[z1,z2,z3,z4,z5,z279])],[(1,[z1,z42,z2,z3,z4,z5]),(1,[z6,z1,z2,z3,z132,z5]),(0,[z6,z1,z99,z2,z3,z93,z4])],[(1,[z45,z1,z2,z3,z4,z38]),(0,[z6,z1,z2,z3,z280,z4,z5])],[]],
   [[(0,[z1,z99,z2,z3,z25,z4,z5])],[(0,[z6,z1,z2,z3,z4,z13,z5]),(0,[z1,z2,z3,z25,z4,z17,z5]),(0,[z6,z1,z2,z281,z3,z4,z5])],[(0,[z1,z42,z2,z3,z282,z4,z5]),(0,[z6,z14,z1,z55,z3,z4,z5]),(1,[z6,z1,z2,z3,z145,z5]),(0,[z6,z2,z3,z4,z49,z5,z38]),(0,[z56,z6,z1,z2,z3,z69,z5]),(0,[z6,z1,z2,z3,z4,z5,z283])],[(0,[z284,z6,z1,z2,z3,z4,z5])],[(0,[z12,z35,z1,z2,z3,z4,z5]),(1,[z12,z1,z2,z3,z25,z5]),(0,[z6,z131,z1,z2,z3,z4,z5])],[(0,[z45,z6,z1,z2,z3,z4,z66]),(0,[z6,z285,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z119,z38]),(0,[z232,z6,z1,z2,z3,z4,z5]),(0,[z147,z6,z1,z2,z286,z4,z5])],[(0,[z287,z6,z1,z2,z3,z4,z5]),(0,[z288,z6,z1,z2,z3,z4,z5]),(0,[z86,z6,z1,z2,z3,z4,z38]),(0,[z6,z1,z2,z3,z4,z148,z66]),(1,[z1,z2,z3,z289,z4,z5]),(0,[z6,z1,z2,z3,z4,z290,z5])],[(0,[z291,z45,z1,z2,z3,z4,z5]),(0,[z292,z6,z1,z2,z3,z4,z5]),(0,[z293,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z294,z3,z4,z5])],[],[(0,[z6,z1,z2,z295,z3,z4,z5]),(0,[z6,z1,z2,z27,z3,z4,z5]),(0,[z296,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z156,z66]),(1,[z6,z1,z2,z275,z4,z5])],[(0,[z73,z1,z2,z118,z3,z4,z5]),(0,[z6,z1,z2,z3,z297,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z15])],[(0,[z298,z6,z1,z2,z3,z4,z5]),(0,[z199,z6,z1,z2,z3,z4,z38]),(0,[z299,z26,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z300,z5])],[(0,[z45,z159,z1,z2,z3,z4,z5]),(1,[z199,z1,z2,z3,z4,z15]),(0,[z6,z1,z2,z3,z4,z109,z5])],[(0,[z6,z1,z2,z3,z153,z4,z5]),(0,[z6,z1,z301,z2,z3,z4,z5]),(1,[z302,z1,z2,z3,z4,z5])],[(0,[z45,z1,z2,z3,z4,z49,z5]),(0,[z45,z28,z1,z2,z3,z4,z5]),(0,[z303,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z50,z3,z4,z5]),(0,[z6,z1,z2,z10,z3,z4,z5])],[(0,[z6,z1,z2,z55,z3,z4,z66]),(0,[z163,z6,z1,z2,z3,z4,z66]),(0,[z6,z1,z2,z3,z157,z4,z5])]],
   [[(0,[z45,z1,z2,z3,z4,z69,z5]),(0,[z1,z209,z2,z3,z25,z4,z5]),(0,[z6,z1,z59,z2,z3,z4,z5]),(0,[z56,z6,z1,z2,z3,z4,z38])],[(0,[z45,z1,z2,z3,z4,z5,z38]),(0,[z6,z1,z2,z3,z304,z4,z5]),(0,[z147,z6,z1,z2,z65,z3,z4])],[(0,[z6,z1,z2,z3,z4,z305,z5])],[(0,[z1,z2,z3,z4,z5,z15,z18])],[(0,[z12,z1,z2,z306,z3,z4,z5]),(0,[z6,z1,z2,z3,z307,z4,z5])],[(0,[z112,z1,z42,z2,z3,z4,z5]),(0,[z6,z1,z308,z2,z3,z4,z5]),(0,[z35,z6,z1,z2,z44,z4,z5]),(0,[z12,z1,z2,z3,z4,z5,z309]),(0,[z6,z1,z2,z310,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z66,z5]),(0,[z6,z1,z2,z3,z4,z38,z311]),(0,[z6,z1,z2,z3,z4,z17,z66]),(0,[z312,z6,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z221,z4,z5,z15]),(0,[z141,z6,z1,z2,z3,z4,z5])],[(0,[z313,z6,z1,z2,z3,z4,z5]),(0,[z314,z6,z1,z2,z3,z4,z5]),(0,[z315,z6,z1,z2,z3,z4,z5]),(0,[z316,z6,z1,z2,z3,z4,z5])],[(0,[z6,z1,z52,z2,z53,z4,z5]),(0,[z6,z164,z1,z2,z3,z4,z5])],[(0,[z73,z1,z42,z2,z3,z4,z5]),(0,[z74,z1,z42,z2,z3,z4,z5]),(1,[z1,z2,z3,z4,z5,z317]),(0,[z80,z6,z1,z2,z3,z318,z5])],[(1,[z26,z1,z2,z3,z4,z5]),(0,[z199,z6,z1,z2,z3,z4,z94]),(1,[z8,z6,z2,z3,z49,z5])],[(0,[z6,z1,z2,z3,z4,z5,z211]),(0,[z8,z45,z1,z2,z3,z4,z5]),(0,[z6,z1,z1,z2,z3,z4,z66]),(0,[z6,z1,z2,z3,z4,z319,z5])],[(0,[z79,z1,z2,z3,z4,z5,z15]),(0,[z199,z6,z1,z2,z3,z4,z15]),(0,[z6,z1,z3,z4,z119,z5,z40])],[(0,[z127,z6,z1,z118,z3,z4,z5]),(0,[z6,z1,z2,z3,z320,z4,z38])],[],[(0,[z321,z1,z2,z3,z25,z4,z5]),(0,[z1,z52,z2,z3,z4,z5,z15]),(0,[z6,z1,z195,z2,z3,z4,z66]),(0,[z6,z322,z1,z2,z3,z4,z5])]],
   [[(0,[z6,z1,z2,z3,z4,z323,z5])],[(0,[z45,z1,z2,z3,z114,z4,z5]),(0,[z324,z1,z2,z3,z25,z4,z5]),(1,[z325,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z286,z4,z5])],[(0,[z6,z1,z2,z3,z187,z4,z5]),(0,[z6,z1,z2,z326,z3,z4,z5]),(1,[z12,z1,z2,z3,z4,z5]),(0,[z141,z6,z1,z327,z3,z4,z5]),(1,[z315,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z328,z4,z5]),(0,[z233,z6,z1,z2,z3,z4,z5])],[(0,[z45,z1,z2,z118,z3,z4,z5]),(0,[z329,z6,z1,z2,z3,z4,z5]),(1,[z268,z1,z2,z3,z4,z5]),(1,[z6,z1,z2,z3,z4,z167]),(0,[z6,z1,z77,z2,z3,z4,z66]),(0,[z6,z191,z1,z2,z3,z4,z5])],[(0,[z330,z1,z2,z3,z25,z4,z5])],[(0,[z24,z1,z2,z3,z4,z5,z15]),(0,[z6,z1,z2,z3,z4,z5,z331])],[(0,[z12,z1,z2,z3,z68,z4,z5]),(0,[z39,z6,z1,z2,z3,z4,z66])],[(0,[z6,z1,z332,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z66,z18]),(0,[z6,z1,z2,z3,z4,z333,z5])],[(0,[z6,z334,z1,z2,z3,z4,z5]),(0,[z335,z6,z1,z2,z3,z4,z5])],[(0,[z336,z6,z1,z2,z3,z4,z5]),(0,[z12,z1,z2,z111,z3,z4,z5]),(0,[z24,z6,z2,z3,z4,z5,z38]),(0,[z6,z1,z2,z3,z4,z5,z337])],[(0,[z1,z42,z99,z2,z3,z4,z5]),(0,[z26,z73,z1,z2,z3,z4,z5]),(0,[z86,z1,z2,z3,z25,z4,z5]),(0,[z6,z1,z2,z3,z4,z338,z5]),(0,[z8,z6,z1,z2,z339,z4,z5]),(0,[z302,z6,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z25,z4,z242,z5]),(0,[z159,z1,z2,z3,z4,z5,z15]),(0,[z6,z1,z2,z3,z340,z4,z5])],[(0,[z129,z45,z1,z2,z3,z4,z5]),(0,[z6,z341,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z342,z3,z4,z5]),(1,[z24,z6,z2,z3,z4,z38]),(0,[z6,z1,z2,z3,z4,z66,z343])],[(0,[z344,z45,z1,z2,z3,z4,z5]),(0,[z12,z1,z2,z3,z11,z4,z5]),(0,[z80,z1,z2,z3,z25,z4,z5]),(0,[z129,z6,z1,z3,z221,z4,z5]),(0,[z1,z2,z3,z4,z116,z5,z345])],[(0,[z26,z1,z2,z44,z3,z4,z5]),(0,[z12,z346,z1,z2,z3,z4,z5]),(0,[z12,z1,z2,z3,z4,z347,z5]),(0,[z1,z2,z65,z3,z4,z5,z15]),(0,[z8,z348,z1,z2,z3,z4,z5])],[(1,[z87,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z65,z3,z4,z17]),(0,[z6,z1,z2,z3,z93,z96,z5])]],
   [[(0,[z6,z1,z349,z2,z3,z4,z5]),(0,[z35,z1,z2,z3,z25,z4,z5]),(0,[z12,z1,z2,z3,z25,z4,z5]),(0,[z8,z6,z1,z2,z3,z11,z5]),(0,[z6,z1,z2,z3,z4,z350,z5])],[(0,[z1,z42,z2,z3,z68,z4,z5]),(0,[z41,z1,z2,z3,z25,z4,z5]),(0,[z351,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z221,z4,z66]),(0,[z219,z6,z1,z2,z3,z4,z66]),(0,[z6,z352,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z353,z4,z5])],[(0,[z45,z1,z42,z2,z3,z4,z5]),(0,[z6,z1,z354,z2,z3,z4,z5]),(0,[z6,z112,z1,z2,z3,z4,z66]),(0,[z6,z1,z2,z355,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z40])],[(0,[z6,z1,z2,z3,z4,z5,z217])],[(0,[z1,z42,z2,z111,z3,z4,z5]),(1,[z1,z2,z3,z25,z4,z38]),(0,[z1,z77,z2,z3,z4,z5,z15])],[(0,[z6,z1,z88,z2,z3,z4,z38]),(0,[z6,z14,z1,z2,z3,z4,z38]),(0,[z141,z6,z1,z2,z68,z4,z5])],[(0,[z154,z1,z42,z2,z3,z4,z5]),(0,[z6,z1,z3,z114,z4,z119,z5])],[(0,[z86,z45,z1,z2,z3,z4,z5]),(0,[z1,z88,z2,z3,z4,z5,z15]),(0,[z35,z1,z2,z3,z46,z4,z5]),(0,[z12,z1,z2,z3,z46,z4,z5]),(0,[z1,z2,z3,z4,z5,z151,z15]),(0,[z26,z26,z1,z2,z3,z4,z5]),(0,[z6,z159,z1,z2,z3,z4,z5]),(1,[z1,z2,z3,z4,z38,z48]),(0,[z6,z1,z2,z3,z4,z66,z96])],[(0,[z1,z42,z2,z3,z11,z4,z5]),(0,[z6,z1,z99,z3,z4,z116,z5])],[(0,[z6,z1,z2,z3,z4,z356,z5]),(0,[z6,z28,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z357,z38]),(0,[z6,z1,z2,z3,z4,z5,z358])],[(0,[z1,z2,z3,z157,z4,z69,z5])],[(0,[z6,z1,z2,z3,z4,z359,z5]),(0,[z6,z1,z2,z3,z4,z360,z5]),(0,[z6,z1,z2,z111,z221,z4,z5])],[(0,[z199,z45,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z275,z3,z4,z5])],[(0,[z6,z361,z1,z2,z3,z4,z5])],[(0,[z362,z6,z1,z2,z3,z4,z5]),(1,[z288,z1,z2,z3,z4,z5]),(0,[z363,z6,z1,z2,z3,z4,z5]),(0,[z226,z28,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z25,z4,z69,z5]),(0,[z364,z6,z1,z2,z3,z4,z5]),(0,[z86,z6,z1,z2,z3,z4,z40]),(1,[z6,z261,z2,z3,z4,z5])]],
   [[(0,[z45,z1,z2,z53,z3,z4,z5]),(0,[z1,z2,z3,z25,z4,z5,z38]),(0,[z202,z1,z2,z3,z11,z4,z5]),(0,[z6,z1,z365,z2,z3,z4,z38])],[(0,[z56,z45,z1,z2,z3,z4,z5]),(1,[z79,z1,z118,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z214,z5]),(1,[z1,z366,z2,z3,z4,z5])],[(0,[z1,z42,z2,z3,z46,z4,z5]),(0,[z79,z6,z1,z2,z3,z4,z66]),(0,[z367,z6,z1,z2,z3,z4,z5]),(0,[z368,z6,z1,z2,z3,z4,z5])],[(0,[z1,z2,z118,z3,z4,z5,z15]),(0,[z39,z1,z2,z3,z4,z5,z15]),(0,[z6,z1,z2,z10,z50,z3,z5])],[(0,[z1,z42,z2,z55,z3,z4,z5]),(0,[z141,z6,z1,z125,z3,z4,z5]),(0,[z86,z6,z1,z2,z3,z4,z116])],[(0,[z6,z1,z2,z3,z180,z4,z5]),(0,[z6,z1,z2,z369,z3,z4,z5]),(0,[z1,z2,z3,z4,z96,z5,z370])],[(0,[z6,z1,z2,z3,z371,z4,z5])],[(0,[z45,z6,z42,z2,z3,z4,z5]),(0,[z127,z6,z1,z2,z3,z4,z5]),(0,[z123,z26,z1,z2,z3,z4,z5]),(0,[z26,z1,z2,z3,z4,z5,z5]),(0,[z6,z1,z2,z372,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z373])],[(0,[z1,z2,z3,z25,z4,z13,z5]),(0,[z374,z6,z1,z2,z3,z4,z5]),(0,[z6,z112,z1,z2,z111,z4,z5])],[(0,[z6,z92,z1,z2,z3,z4,z38]),(0,[z6,z1,z2,z375,z3,z4,z5]),(1,[z376,z1,z2,z3,z4,z5]),(0,[z26,z1,z2,z3,z93,z4,z5]),(0,[z377,z6,z1,z2,z3,z4,z5])],[(0,[z1,z42,z2,z3,z4,z17,z5]),(0,[z45,z1,z2,z3,z4,z5,z40]),(1,[z6,z14,z77,z3,z4,z5]),(1,[z130,z1,z2,z3,z4,z5]),(0,[z6,z1,z378,z2,z3,z4,z5])],[(0,[z6,z1,z2,z3,z4,z5,z379]),(0,[z141,z1,z2,z3,z4,z5,z15]),(0,[z80,z6,z2,z55,z3,z4,z5]),(0,[z24,z6,z1,z2,z3,z4,z66]),(0,[z126,z1,z2,z3,z4,z96,z5])],[(0,[z380,z6,z1,z2,z3,z4,z5]),(0,[z381,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z114,z4,z5])],[(0,[z382,z6,z1,z2,z3,z4,z5]),(0,[z26,z1,z383,z2,z3,z4,z5])],[(0,[z384,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z118,z3,z4,z5]),(0,[z1,z2,z3,z68,z25,z4,z5]),(0,[z6,z1,z385,z2,z3,z4,z5]),(0,[z6,z1,z386,z2,z3,z4,z5])],[(0,[z147,z6,z1,z2,z3,z4,z38])]],
   [[(0,[z6,z387,z1,z2,z3,z4,z5]),(0,[z80,z6,z1,z2,z388,z4,z5])],[(0,[z8,z1,z2,z3,z25,z4,z5]),(0,[z1,z2,z3,z25,z4,z5,z15]),(0,[z6,z1,z2,z3,z4,z389,z5]),(0,[z6,z1,z2,z3,z4,z49,z66]),(0,[z390,z6,z1,z2,z3,z4,z5]),(0,[z86,z6,z1,z3,z4,z5,z40])],[(0,[z45,z1,z2,z3,z4,z96,z5]),(0,[z1,z2,z3,z4,z13,z5,z15]),(0,[z6,z1,z2,z3,z4,z5,z391]),(0,[z6,z1,z2,z3,z4,z5,z392])],[(0,[z26,z1,z2,z3,z4,z119,z5]),(0,[z256,z1,z2,z3,z4,z5,z38]),(0,[z6,z1,z2,z3,z4,z69,z66]),(0,[z6,z1,z2,z3,z393,z4,z5])],[(0,[z394,z6,z1,z2,z3,z4,z5]),(0,[z1,z395,z42,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z396,z5])],[(0,[z6,z1,z2,z3,z4,z397,z5]),(0,[z6,z1,z2,z398,z3,z4,z5])],[(1,[z1,z2,z3,z4,z5,z370])],[(0,[z6,z1,z399,z2,z3,z4,z5]),(0,[z315,z1,z2,z3,z4,z66,z5]),(0,[z6,z1,z2,z3,z4,z400,z5]),(0,[z6,z1,z2,z3,z4,z5,z401]),(1,[z6,z1,z2,z286,z4,z5])],[(0,[z1,z42,z77,z2,z3,z4,z5]),(1,[z1,z42,z2,z3,z4,z66]),(0,[z26,z127,z1,z2,z3,z4,z5]),(0,[z6,z402,z1,z2,z3,z4,z5]),(0,[z98,z1,z2,z3,z4,z5,z122])],[(0,[z37,z6,z1,z2,z3,z4,z5]),(0,[z403,z6,z1,z2,z3,z4,z5])],[(0,[z19,z6,z92,z2,z3,z4,z5]),(0,[z6,z404,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z405,z4,z5]),(1,[z1,z2,z3,z4,z235,z5])],[(0,[z6,z1,z2,z3,z406,z4,z5]),(0,[z6,z1,z2,z3,z170,z4,z5])],[(0,[z6,z1,z2,z3,z4,z13,z66]),(0,[z1,z2,z3,z25,z4,z66,z5]),(0,[z6,z1,z209,z2,z3,z119,z5]),(0,[z39,z191,z1,z2,z3,z4,z5])],[(0,[z6,z1,z42,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z407,z5]),(0,[z12,z1,z52,z2,z3,z4,z5]),(0,[z1,z2,z55,z3,z25,z4,z5]),(0,[z6,z1,z2,z111,z4,z69,z5]),(0,[z6,z1,z2,z65,z3,z4,z38]),(0,[z6,z1,z209,z2,z3,z4,z5])],[(0,[z6,z1,z408,z2,z3,z4,z5]),(0,[z409,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z78]),(0,[z410,z6,z1,z2,z3,z4,z5]),(0,[z411,z6,z1,z2,z3,z4,z5])],[(0,[z6,z1,z2,z412,z3,z4,z5])]],
   [[(0,[z79,z1,z2,z118,z3,z4,z5])],[(0,[z174,z26,z1,z2,z3,z4,z5])],[(0,[z12,z1,z99,z2,z3,z4,z5]),(0,[z129,z1,z2,z3,z25,z4,z5]),(0,[z1,z2,z3,z4,z94,z5,z15]),(0,[z80,z6,z1,z77,z3,z4,z5])],[(0,[z6,z28,z1,z2,z3,z4,z413]),(1,[z1,z2,z3,z4,z5,z345])],[(0,[z6,z1,z414,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z82,z119]),(0,[z6,z1,z2,z3,z4,z415,z5])],[(0,[z6,z1,z2,z3,z4,z416,z38]),(1,[z417,z1,z2,z3,z4,z5]),(1,[z6,z1,z209,z3,z119,z5])],[(0,[z6,z1,z2,z3,z418,z4,z5]),(0,[z6,z1,z2,z3,z289,z4,z5])],[(0,[z419,z6,z1,z2,z3,z4,z5]),(0,[z6,z420,z1,z2,z3,z4,z5])],[(0,[z1,z42,z52,z2,z3,z4,z5]),(0,[z12,z24,z1,z2,z3,z4,z5]),(1,[z1,z2,z3,z4,z421,z5]),(0,[z6,z1,z2,z3,z422,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z423])],[(0,[z12,z1,z2,z3,z4,z5,z122]),(0,[z6,z1,z2,z3,z424,z4,z5]),(0,[z6,z77,z2,z55,z3,z4,z5]),(0,[z6,z1,z2,z425,z3,z4,z5]),(0,[z6,z1,z2,z50,z3,z4,z66]),(0,[z6,z1,z2,z10,z3,z4,z66]),(0,[z39,z6,z1,z99,z3,z4,z5])],[(0,[z6,z1,z2,z3,z4,z426,z5]),(1,[z1,z427,z2,z3,z4,z5])],[(1,[z428,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z53,z3,z4,z5])],[(0,[z141,z6,z1,z2,z3,z4,z51]),(0,[z6,z1,z2,z429,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z430])],[(0,[z202,z6,z1,z2,z3,z4,z5]),(1,[z431,z1,z2,z3,z4,z5]),(0,[z6,z159,z2,z3,z4,z49,z5])],[(0,[z6,z1,z2,z432,z3,z4,z5])],[(0,[z79,z1,z42,z2,z3,z4,z5]),(0,[z6,z1,z2,z433,z3,z4,z5]),(0,[z6,z1,z52,z2,z221,z4,z5]),(0,[z6,z1,z2,z434,z3,z4,z5]),(0,[z6,z1,z2,z435,z3,z4,z5])]],
   [[(0,[z73,z1,z2,z44,z3,z4,z5]),(0,[z12,z1,z139,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z66,z66])],[(0,[z141,z6,z1,z2,z3,z4,z66])],[(1,[z1,z395,z2,z3,z4,z5]),(0,[z199,z1,z2,z3,z25,z4,z5]),(0,[z6,z28,z2,z3,z4,z5,z38]),(0,[z436,z6,z1,z2,z3,z4,z5]),(0,[z313,z6,z1,z2,z3,z4,z66]),(0,[z315,z6,z1,z2,z3,z4,z66])],[(0,[z19,z6,z1,z2,z3,z4,z63]),(0,[z6,z1,z2,z3,z4,z337,z38])],[(0,[z1,z42,z2,z3,z4,z5,z122]),(1,[z1,z2,z3,z4,z5,z437]),(0,[z6,z1,z2,z3,z4,z5,z179]),(0,[z1,z2,z3,z4,z5,z38,z48]),(0,[z6,z1,z438,z2,z3,z4,z5]),(0,[z6,z1,z2,z439,z3,z4,z5])],[(0,[z45,z1,z2,z3,z4,z440,z5]),(0,[z45,z1,z209,z2,z3,z4,z5]),(0,[z74,z6,z1,z2,z3,z13,z5]),(1,[z26,z1,z2,z3,z4,z66]),(0,[z6,z1,z2,z441,z3,z4,z5])],[],[(0,[z6,z1,z442,z2,z3,z4,z5]),(0,[z56,z1,z2,z3,z25,z4,z5]),(0,[z1,z2,z53,z3,z4,z5,z15]),(0,[z6,z1,z2,z3,z443,z4,z5]),(1,[z6,z1,z2,z3,z4,z182])],[(0,[z24,z1,z42,z2,z3,z4,z5]),(0,[z1,z42,z2,z3,z4,z5,z48]),(0,[z6,z1,z2,z2,z3,z4,z5]),(0,[z28,z1,z2,z3,z25,z4,z5]),(1,[z229,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z25,z4,z5,z40]),(0,[z6,z444,z1,z2,z3,z4,z5])],[],[(0,[z45,z1,z2,z3,z4,z445,z5]),(0,[z1,z88,z2,z118,z3,z4,z5]),(0,[z446,z6,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z66,z5,z15]),(0,[z26,z6,z1,z2,z3,z4,z38])],[(0,[z127,z1,z2,z3,z4,z5,z15]),(0,[z12,z1,z2,z55,z3,z4,z5]),(0,[z1,z2,z3,z153,z4,z5,z15]),(0,[z141,z6,z112,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z447,z5])],[(1,[z12,z1,z2,z3,z4,z66]),(1,[z315,z1,z2,z3,z4,z66]),(0,[z6,z1,z2,z448,z3,z4,z5]),(0,[z449,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z96,z5])],[(0,[z159,z1,z42,z2,z3,z4,z5]),(0,[z1,z42,z2,z3,z4,z148,z5]),(0,[z6,z1,z2,z3,z4,z450,z5])],[(0,[z12,z6,z1,z2,z3,z25,z5]),(0,[z451,z6,z1,z2,z3,z4,z5])]],
   [[(0,[z147,z45,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z25,z4,z49,z5])],[(0,[z41,z6,z1,z2,z4,z5,z18])],[(0,[z12,z1,z2,z3,z4,z17,z5]),(0,[z452,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z66,z453]),(0,[z6,z1,z2,z4,z69,z5,z18])],[(0,[z26,z1,z88,z2,z3,z4,z5]),(0,[z26,z14,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z11,z69,z5])],[(0,[z19,z6,z1,z2,z3,z4,z5]),(1,[z110,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z327,z3,z4,z5]),(0,[z454,z6,z1,z2,z3,z4,z5]),(0,[z56,z6,z1,z2,z4,z5,z18])],[(0,[z6,z455,z1,z2,z3,z4,z5]),(0,[z141,z6,z1,z2,z3,z120,z5]),(0,[z6,z1,z2,z3,z4,z116,z38]),(0,[z6,z1,z2,z3,z4,z338,z66])],[],[(0,[z6,z1,z2,z3,z4,z456,z5]),(0,[z6,z1,z457,z2,z3,z4,z5]),(0,[z6,z1,z458,z2,z3,z4,z5])],[(1,[z6,z1,z2,z65,z4,z17])],[(0,[z459,z6,z1,z2,z3,z4,z5]),(0,[z45,z1,z2,z44,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z460,z5]),(0,[z80,z6,z1,z2,z3,z4,z461]),(0,[z6,z1,z2,z3,z4,z462,z5])],[(0,[z26,z6,z1,z2,z3,z4,z94]),(0,[z6,z1,z2,z3,z68,z4,z38]),(0,[z6,z1,z2,z53,z68,z4,z5]),(0,[z6,z1,z261,z2,z3,z4,z5])],[(0,[z1,z2,z3,z114,z4,z5,z15]),(0,[z463,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z464,z3,z4,z5]),(0,[z106,z6,z1,z2,z3,z4,z5])],[(0,[z79,z26,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z465]),(0,[z321,z6,z1,z2,z3,z4,z5]),(0,[z26,z6,z1,z2,z3,z4,z15]),(0,[z466,z6,z1,z2,z3,z4,z5]),(0,[z6,z159,z2,z3,z4,z66,z5]),(0,[z98,z6,z1,z2,z3,z4,z5])],[],[(0,[z324,z6,z1,z2,z3,z4,z5]),(0,[z37,z1,z2,z3,z4,z5,z15]),(0,[z6,z1,z52,z55,z3,z4,z5])],[(0,[z1,z42,z2,z3,z4,z175,z5])]],
   [[(0,[z467,z45,z1,z2,z3,z4,z5]),(0,[z12,z1,z77,z2,z3,z4,z5]),(0,[z8,z6,z1,z468,z3,z4,z5]),(0,[z469,z6,z1,z2,z3,z4,z5]),(0,[z147,z6,z1,z2,z3,z93,z5])],[(0,[z1,z42,z2,z3,z4,z13,z5]),(0,[z45,z1,z2,z3,z4,z5,z317]),(0,[z6,z1,z2,z3,z4,z5,z197]),(0,[z6,z1,z2,z470,z3,z4,z5]),(0,[z330,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z94,z38]),(0,[z6,z1,z2,z3,z471,z4,z5])],[(0,[z1,z2,z50,z3,z25,z4,z5]),(0,[z472,z6,z1,z2,z3,z4,z5]),(1,[z6,z159,z2,z3,z4,z66]),(0,[z6,z159,z1,z2,z3,z4,z66])],[(0,[z12,z1,z2,z10,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z38,z122]),(0,[z6,z1,z2,z473,z3,z4,z5])],[(0,[z6,z1,z2,z3,z25,z4,z38]),(0,[z6,z28,z1,z2,z3,z4,z66])],[(0,[z24,z26,z1,z2,z3,z4,z5]),(0,[z474,z6,z1,z2,z3,z4,z5])],[(0,[z39,z1,z42,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z475])],[(0,[z26,z92,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z476,z5]),(1,[z436,z1,z2,z3,z4,z5]),(1,[z411,z6,z1,z2,z3,z4]),(0,[z86,z6,z1,z2,z3,z4,z5])],[(0,[z12,z56,z1,z2,z3,z4,z5]),(1,[z177,z1,z2,z3,z4,z5]),(0,[z428,z6,z1,z2,z3,z4,z5]),(0,[z6,z477,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z478,z4,z5])],[],[(0,[z1,z42,z2,z3,z4,z5,z15]),(0,[z73,z127,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z479,z3,z4,z5]),(0,[z12,z1,z2,z3,z4,z66,z5]),(0,[z80,z6,z1,z2,z3,z4,z5])],[],[(0,[z480,z6,z1,z2,z3,z4,z5]),(0,[z14,z1,z2,z3,z25,z4,z5]),(0,[z26,z1,z2,z3,z4,z5,z18]),(0,[z6,z1,z481,z2,z3,z4,z5])],[(0,[z35,z6,z1,z2,z3,z4,z5]),(0,[z12,z1,z218,z2,z3,z4,z5]),(0,[z12,z6,z1,z2,z3,z4,z5]),(0,[z6,z482,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z279,z122])],[(0,[z141,z1,z42,z2,z3,z4,z5]),(0,[z1,z42,z2,z50,z3,z4,z5]),(0,[z1,z42,z2,z10,z3,z4,z5]),(0,[z12,z1,z2,z3,z221,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z246]),(0,[z56,z70,z1,z2,z3,z4,z5]),(0,[z41,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z483])],[(0,[z12,z112,z1,z2,z3,z4,z5]),(0,[z26,z484,z1,z2,z3,z4,z5]),(0,[z6,z1,z485,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z486]),(0,[z6,z1,z2,z3,z4,z5,z279])]],
   [[(0,[z6,z1,z2,z3,z4,z440,z5]),(0,[z6,z1,z2,z3,z4,z5,z75]),(0,[z6,z1,z2,z369,z3,z4,z66]),(0,[z6,z1,z2,z3,z487,z4,z5])],[(0,[z6,z1,z2,z3,z4,z9,z5]),(1,[z6,z1,z2,z3,z4,z38]),(0,[z6,z1,z366,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z488])],[(0,[z127,z6,z1,z2,z3,z4,z66]),(0,[z1,z99,z2,z3,z4,z5,z15]),(1,[z348,z1,z2,z3,z4,z5]),(0,[z6,z1,z489,z2,z3,z4,z5]),(0,[z56,z490,z1,z2,z3,z4,z5])],[(1,[z1,z2,z3,z491,z4,z5]),(0,[z6,z1,z2,z3,z4,z492,z5])],[(0,[z45,z1,z2,z3,z93,z4,z5]),(0,[z1,z2,z3,z4,z66,z5,z217]),(0,[z493,z1,z2,z3,z4,z17,z5])],[(0,[z1,z42,z2,z3,z4,z66,z5])],[(0,[z6,z1,z2,z3,z4,z445,z5]),(0,[z6,z1,z494,z2,z3,z4,z5])],[(0,[z6,z1,z2,z495,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z97]),(0,[z8,z133,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z114,z4,z66])],[(1,[z45,z92,z2,z3,z4,z5]),(0,[z6,z1,z2,z496,z3,z4,z5]),(0,[z387,z1,z2,z3,z25,z4,z5])],[(0,[z1,z42,z2,z3,z221,z4,z5]),(0,[z6,z1,z2,z118,z3,z4,z66]),(0,[z6,z1,z2,z3,z4,z497,z5])],[(0,[z291,z6,z1,z2,z3,z4,z5]),(1,[z1,z2,z3,z4,z5,z309]),(0,[z6,z1,z2,z220,z3,z4,z5])],[(0,[z6,z1,z2,z3,z498,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z499]),(0,[z26,z1,z2,z65,z3,z4,z5]),(0,[z6,z1,z2,z3,z339,z4,z5]),(1,[z256,z1,z2,z3,z4,z38]),(0,[z6,z1,z2,z3,z4,z447,z69])],[(0,[z26,z45,z1,z2,z3,z4,z5]),(0,[z79,z6,z1,z88,z3,z4,z5]),(0,[z390,z6,z1,z2,z3,z4,z66]),(0,[z130,z6,z1,z2,z3,z4,z5])],[(0,[z500,z6,z1,z2,z3,z4,z5]),(0,[z501,z6,z1,z2,z3,z4,z5]),(0,[z105,z6,z1,z2,z3,z4,z5])],[(0,[z45,z1,z2,z3,z4,z119,z5]),(0,[z6,z1,z2,z3,z502,z4,z5])],[(1,[z1,z2,z3,z4,z66,z15]),(0,[z8,z6,z1,z425,z3,z4,z5]),(0,[z6,z1,z2,z503,z3,z4,z5])]],
   [[(0,[z6,z1,z2,z3,z4,z397,z66])],[(0,[z6,z504,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z505]),(0,[z6,z1,z2,z506,z3,z4,z5])],[(0,[z12,z1,z2,z253,z3,z4,z5]),(0,[z1,z209,z2,z3,z4,z5,z15]),(0,[z24,z6,z159,z2,z3,z4,z5])],[(0,[z6,z1,z507,z2,z3,z4,z5]),(0,[z288,z12,z1,z2,z3,z4,z5]),(0,[z39,z26,z1,z2,z3,z4,z5]),(0,[z129,z171,z1,z2,z3,z4,z5]),(0,[z41,z6,z1,z2,z65,z4,z5])],[(0,[z6,z1,z2,z43,z3,z4,z5]),(0,[z6,z1,z2,z44,z3,z4,z5]),(0,[z508,z6,z1,z2,z3,z4,z5]),(0,[z6,z509,z1,z2,z3,z4,z5]),(0,[z37,z6,z1,z2,z3,z4,z66])],[],[(0,[z147,z1,z2,z3,z25,z4,z5]),(0,[z6,z1,z2,z3,z510,z4,z5]),(0,[z240,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z511,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z370])],[(1,[z233,z1,z2,z3,z4,z5])],[(0,[z6,z1,z42,z2,z3,z4,z66]),(0,[z45,z1,z2,z512,z3,z4,z5]),(0,[z6,z1,z2,z513,z3,z4,z5]),(0,[z6,z1,z209,z2,z3,z4,z66])],[(0,[z19,z1,z2,z3,z4,z5,z15]),(0,[z6,z1,z2,z514,z3,z4,z5]),(0,[z515,z6,z1,z2,z3,z4,z5]),(0,[z1,z2,z516,z3,z4,z5,z15]),(0,[z428,z1,z2,z3,z4,z49,z5]),(1,[z1,z2,z3,z4,z5,z517])],[(0,[z1,z2,z3,z4,z69,z5,z15]),(0,[z6,z1,z2,z3,z4,z235,z5]),(0,[z518,z6,z1,z2,z3,z4,z5]),(0,[z106,z6,z1,z2,z3,z4,z69])],[(0,[z6,z1,z3,z4,z116,z5,z40])],[(0,[z6,z1,z2,z3,z4,z5,z317]),(0,[z6,z1,z2,z3,z4,z5,z519]),(0,[z6,z1,z2,z520,z3,z4,z5])],[(0,[z73,z6,z1,z2,z3,z4,z38]),(0,[z74,z6,z1,z2,z3,z4,z38]),(0,[z6,z1,z2,z3,z4,z38,z207])],[(0,[z521,z6,z1,z2,z3,z4,z5]),(0,[z12,z1,z2,z3,z4,z49,z5]),(0,[z234,z6,z1,z2,z3,z4,z5]),(0,[z8,z6,z1,z2,z3,z4,z5]),(1,[z129,z6,z1,z221,z4,z5]),(0,[z6,z1,z209,z3,z4,z119,z5])],[(0,[z81,z6,z1,z2,z3,z4,z38]),(0,[z493,z6,z1,z2,z3,z4,z5])]],
   [[(0,[z12,z1,z2,z3,z4,z69,z5])],[(0,[z12,z1,z2,z3,z4,z5,z38]),(1,[z1,z2,z3,z4,z5,z522]),(0,[z268,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z523,z2,z3,z4,z5]),(0,[z6,z1,z52,z2,z3,z4,z38]),(0,[z6,z1,z2,z3,z418,z4,z66])],[(0,[z524,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z525,z3,z4,z5]),(0,[z159,z1,z366,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z526,z4,z5])],[(1,[z6,z1,z2,z3,z4,z211]),(0,[z141,z12,z1,z2,z3,z4,z5]),(0,[z527,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z528,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z345])],[(0,[z1,z2,z44,z3,z25,z4,z5]),(0,[z314,z12,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z25,z4,z96,z5])],[(1,[z1,z2,z3,z25,z4,z5]),(0,[z112,z1,z427,z2,z3,z4,z5])],[(0,[z79,z1,z2,z44,z3,z4,z5]),(0,[z6,z1,z99,z2,z3,z4,z38]),(0,[z6,z1,z2,z53,z3,z4,z66]),(0,[z6,z1,z2,z3,z4,z5,z529]),(1,[z86,z6,z1,z3,z4,z40])],[(0,[z6,z1,z2,z3,z530,z4,z5]),(0,[z6,z1,z2,z50,z4,z69,z5]),(0,[z6,z1,z2,z10,z4,z69,z5])],[(0,[z531,z1,z2,z3,z4,z5,z15]),(0,[z1,z2,z3,z491,z221,z4,z5]),(0,[z532,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z533,z4,z5])],[(0,[z1,z42,z2,z3,z4,z49,z5]),(0,[z12,z1,z2,z3,z4,z13,z5]),(0,[z534,z6,z1,z2,z3,z4,z5])],[(0,[z535,z6,z1,z2,z3,z4,z5]),(0,[z141,z6,z1,z2,z111,z4,z5]),(0,[z6,z1,z427,z2,z3,z4,z5])],[(0,[z1,z42,z2,z3,z4,z69,z5]),(0,[z6,z1,z2,z3,z536,z4,z5])],[(0,[z1,z42,z2,z3,z4,z5,z38]),(1,[z39,z6,z1,z3,z114,z5])],[(0,[z35,z6,z1,z2,z46,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z5]),(0,[z6,z431,z1,z2,z3,z4,z5]),(0,[z41,z131,z1,z2,z3,z4,z5])],[(0,[z6,z14,z77,z2,z3,z4,z5]),(0,[z6,z1,z2,z537,z3,z4,z5])],[(0,[z127,z1,z42,z2,z3,z4,z5]),(0,[z6,z538,z1,z2,z3,z4,z5]),(0,[z80,z1,z2,z3,z4,z5,z15]),(0,[z6,z1,z539,z2,z3,z4,z5]),(0,[z129,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z93,z4,z5])]],
   [[(0,[z1,z540,z42,z2,z3,z4,z5]),(0,[z344,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z541,z5]),(0,[z376,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z111,z3,z4,z38]),(0,[z1,z2,z3,z187,z11,z4,z5])],[(0,[z6,z1,z2,z3,z4,z542,z5]),(0,[z6,z14,z1,z77,z3,z4,z5])],[(1,[z45,z1,z2,z3,z4,z5]),(0,[z543,z6,z1,z2,z3,z4,z5]),(0,[z35,z1,z2,z3,z4,z5,z15]),(0,[z12,z1,z2,z3,z4,z5,z15]),(0,[z6,z1,z2,z3,z4,z5,z544])],[(0,[z1,z308,z42,z2,z3,z4,z5]),(0,[z1,z2,z3,z187,z25,z4,z5]),(0,[z41,z1,z2,z3,z4,z5,z15]),(0,[z26,z1,z2,z3,z4,z116,z5]),(0,[z6,z1,z383,z2,z3,z4,z5])],[(0,[z256,z26,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z545,z3,z4,z5]),(0,[z6,z1,z2,z3,z546,z4,z5]),(0,[z6,z1,z2,z3,z11,z4,z38]),(0,[z436,z159,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z119,z5,z15]),(0,[z1,z2,z3,z4,z5,z15,z122]),(0,[z80,z6,z1,z2,z3,z4,z158]),(0,[z6,z547,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z548,z5])],[(0,[z45,z6,z1,z2,z3,z4,z38]),(0,[z6,z1,z2,z549,z3,z4,z5]),(0,[z12,z1,z2,z50,z3,z4,z5]),(0,[z1,z2,z3,z93,z4,z5,z15]),(0,[z6,z1,z2,z3,z4,z461,z5]),(0,[z6,z1,z2,z550,z3,z4,z5])],[(1,[z6,z2,z3,z4,z49,z38])],[(0,[z6,z1,z2,z3,z4,z551,z5]),(0,[z26,z1,z2,z3,z68,z4,z5]),(1,[z1,z2,z3,z4,z66,z217]),(0,[z6,z1,z2,z3,z4,z5,z552]),(1,[z493,z1,z2,z3,z4,z5])],[(1,[z6,z1,z2,z3,z4,z179]),(0,[z6,z1,z2,z3,z4,z119,z5])],[(0,[z553,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z554,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z4,z5]),(0,[z6,z1,z2,z3,z4,z38,z48]),(0,[z6,z1,z2,z3,z4,z5,z555])],[(0,[z556,z6,z1,z2,z3,z4,z5]),(0,[z6,z557,z1,z2,z3,z4,z5])],[(0,[z6,z1,z2,z53,z111,z4,z5])],[(0,[z6,z1,z2,z3,z4,z558,z5]),(0,[z6,z1,z2,z3,z4,z559,z5])],[(0,[z45,z14,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z46,z4,z38])],[(0,[z19,z6,z1,z2,z3,z4,z66]),(0,[z64,z6,z1,z2,z3,z4,z5]),(0,[z199,z6,z1,z2,z3,z4,z5]),(0,[z26,z1,z2,z3,z11,z4,z5]),(0,[z26,z1,z2,z3,z4,z94,z5]),(0,[z6,z1,z2,z3,z4,z5,z18]),(0,[z147,z6,z1,z62,z3,z4,z5])]],
   [[(0,[z6,z1,z2,z55,z3,z4,z38]),(0,[z6,z1,z2,z3,z560,z4,z5]),(0,[z6,z561,z1,z2,z3,z4,z5])],[(0,[z37,z1,z42,z2,z3,z4,z5]),(0,[z1,z88,z2,z44,z3,z4,z5]),(1,[z6,z1,z2,z339,z4,z5])],[(0,[z26,z1,z2,z3,z25,z4,z5]),(0,[z6,z484,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z562,z38])],[(0,[z6,z1,z2,z512,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z563,z5])],[(0,[z6,z1,z2,z3,z4,z564,z5]),(0,[z26,z74,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z565,z3,z4,z5]),(0,[z6,z1,z566,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z567,z4,z5]),(0,[z56,z6,z1,z2,z3,z4,z5])],[(1,[z6,z1,z2,z50,z69,z5]),(0,[z568,z6,z1,z2,z3,z4,z5])],[(0,[z6,z1,z2,z3,z4,z569,z5]),(0,[z141,z6,z1,z2,z3,z145,z5]),(0,[z6,z1,z2,z3,z4,z17,z38])],[],[],[(0,[z26,z1,z2,z3,z46,z4,z5]),(0,[z6,z1,z2,z3,z570,z4,z5]),(1,[z226,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z66,z122]),(0,[z571,z6,z1,z2,z3,z4,z5])],[(0,[z213,z6,z1,z2,z3,z4,z5])],[(0,[z6,z1,z2,z3,z4,z38,z38])],[(1,[z74,z1,z2,z3,z25,z5]),(0,[z6,z1,z1,z2,z3,z4,z38]),(1,[z70,z1,z2,z3,z4,z5])],[(0,[z6,z1,z55,z3,z4,z119,z5])],[(0,[z73,z45,z1,z2,z3,z4,z5]),(0,[z288,z26,z1,z2,z3,z4,z5])],[(0,[z419,z1,z42,z2,z3,z4,z5])]],
   [[(0,[z79,z127,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z68,z4,z5,z15]),(1,[z1,z2,z3,z4,z15,z38]),(0,[z6,z1,z2,z146,z3,z4,z5])],[(0,[z6,z1,z2,z3,z4,z572,z5]),(0,[z6,z1,z573,z2,z3,z4,z5]),(0,[z1,z162,z2,z3,z4,z5,z15]),(0,[z6,z1,z2,z3,z320,z4,z5]),(0,[z325,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z93,z4,z96])],[(0,[z45,z92,z1,z2,z3,z4,z5]),(0,[z86,z6,z1,z2,z3,z4,z66])],[(0,[z89,z45,z1,z2,z3,z4,z5]),(0,[z8,z1,z2,z3,z4,z5,z15]),(0,[z41,z6,z1,z2,z3,z4,z18])],[(1,[z6,z1,z2,z3,z318,z5]),(0,[z6,z1,z77,z2,z3,z4,z38]),(0,[z28,z1,z34,z2,z3,z4,z5])],[(0,[z1,z42,z2,z3,z187,z4,z5]),(0,[z92,z1,z2,z3,z25,z4,z5]),(0,[z80,z6,z1,z2,z3,z4,z66]),(0,[z6,z1,z2,z574,z3,z4,z5]),(0,[z6,z2,z3,z4,z66,z5,z38])],[(0,[z287,z12,z1,z2,z3,z4,z5]),(1,[z575,z1,z2,z3,z4,z5]),(1,[z6,z2,z3,z4,z66,z38])],[(1,[z19,z42,z2,z3,z4,z5]),(0,[z45,z1,z2,z3,z4,z5,z18]),(0,[z576,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z413]),(1,[z147,z6,z1,z2,z3,z122])],[(0,[z45,z1,z577,z2,z3,z4,z5]),(0,[z35,z6,z1,z2,z3,z4,z66]),(0,[z12,z6,z1,z2,z3,z4,z66]),(0,[z6,z177,z1,z2,z3,z4,z5]),(0,[z8,z6,z1,z2,z310,z4,z5])],[(0,[z578,z45,z1,z2,z3,z4,z5]),(0,[z41,z6,z1,z2,z3,z4,z66]),(0,[z6,z1,z2,z3,z4,z5,z579]),(0,[z56,z6,z1,z2,z65,z4,z5])],[(0,[z580,z6,z1,z2,z3,z4,z5]),(0,[z12,z1,z2,z3,z4,z5,z40]),(1,[z6,z1,z2,z3,z4,z391]),(0,[z6,z1,z2,z3,z4,z5,z581])],[(0,[z1,z42,z2,z53,z3,z4,z5]),(0,[z6,z92,z1,z2,z3,z4,z499]),(0,[z1,z2,z3,z46,z25,z4,z5]),(0,[z582,z6,z1,z2,z3,z4,z5]),(0,[z14,z1,z32,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z583,z5])],[(0,[z6,z159,z28,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z584,z4,z5])],[],[(0,[z26,z1,z2,z31,z3,z4,z5]),(0,[z141,z26,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z585])],[(0,[z6,z1,z2,z3,z586,z4,z5]),(0,[z12,z159,z1,z2,z3,z4,z5]),(0,[z6,z587,z1,z2,z3,z4,z5]),(0,[z39,z6,z1,z209,z3,z4,z5]),(0,[z6,z1,z99,z2,z3,z4,z40]),(0,[z6,z1,z2,z3,z588,z4,z5]),(0,[z6,z1,z589,z2,z3,z4,z5])]],
   [[(0,[z1,z2,z10,z3,z25,z4,z5]),(0,[z6,z1,z2,z590,z3,z4,z5]),(1,[z6,z1,z2,z3,z4,z447]),(0,[z6,z1,z2,z3,z4,z5,z591]),(0,[z288,z1,z2,z3,z93,z4,z5])],[(0,[z12,z28,z1,z2,z3,z4,z5]),(0,[z592,z6,z1,z2,z3,z4,z5])],[(0,[z6,z348,z1,z2,z3,z4,z5]),(0,[z417,z6,z1,z2,z3,z4,z5])],[(0,[z1,z42,z349,z2,z3,z4,z5]),(0,[z56,z6,z1,z2,z68,z4,z5]),(0,[z6,z1,z2,z593,z3,z4,z5]),(0,[z6,z112,z1,z2,z3,z4,z38]),(0,[z417,z1,z2,z3,z221,z4,z5])],[(0,[z1,z172,z2,z3,z25,z4,z5]),(0,[z129,z1,z2,z3,z4,z5,z15]),(1,[z6,z1,z468,z3,z4,z5]),(0,[z6,z1,z99,z2,z3,z4,z116]),(1,[z6,z1,z2,z3,z93,z96])],[(0,[z1,z42,z2,z3,z4,z5,z40]),(0,[z6,z1,z2,z224,z3,z4,z5]),(0,[z376,z1,z2,z3,z4,z5,z15])],[(0,[z45,z1,z2,z65,z3,z4,z5]),(0,[z37,z12,z1,z2,z3,z4,z5]),(1,[z12,z1,z2,z3,z13,z5]),(0,[z80,z234,z1,z2,z3,z4,z5])],[(0,[z45,z45,z1,z2,z3,z4,z5]),(0,[z39,z6,z1,z55,z3,z4,z5])],[(0,[z6,z1,z594,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z158])],[(0,[z6,z1,z88,z2,z3,z4,z5]),(0,[z73,z6,z1,z2,z44,z4,z5]),(0,[z6,z14,z1,z2,z3,z4,z5])],[(0,[z6,z1,z595,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z596,z4,z5])],[(0,[z6,z1,z2,z597,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z421,z5]),(0,[z598,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z599,z3,z4,z5]),(0,[z1,z2,z3,z4,z17,z5,z517])],[(0,[z19,z1,z42,z2,z3,z4,z5]),(1,[z35,z1,z2,z46,z4,z5])],[(0,[z1,z42,z2,z3,z4,z96,z5]),(0,[z6,z1,z2,z3,z4,z600,z5]),(0,[z250,z6,z1,z2,z3,z4,z5])],[(0,[z1,z2,z44,z3,z46,z4,z5]),(1,[z6,z1,z2,z3,z4,z214]),(0,[z6,z1,z601,z2,z3,z4,z5])],[(0,[z6,z1,z2,z44,z3,z4,z66]),(0,[z86,z1,z2,z3,z4,z5,z15]),(0,[z6,z1,z2,z3,z4,z66,z15]),(0,[z26,z1,z52,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z602,z5])]],
   [[(0,[z6,z1,z2,z603,z3,z4,z5]),(0,[z6,z1,z2,z3,z604,z4,z5]),(1,[z6,z1,z2,z3,z4,z499]),(0,[z605,z6,z1,z2,z3,z4,z5])],[(0,[z95,z6,z1,z2,z3,z4,z5]),(0,[z606,z6,z1,z2,z3,z4,z5])],[(0,[z607,z6,z1,z2,z3,z4,z5])],[(0,[z79,z6,z1,z2,z3,z4,z38])],[(0,[z12,z1,z2,z3,z114,z4,z5]),(0,[z199,z1,z2,z3,z4,z5,z15]),(0,[z26,z1,z99,z2,z3,z4,z5]),(0,[z6,z1,z365,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z120,z4,z5])],[(0,[z6,z1,z395,z2,z3,z4,z5]),(0,[z6,z1,z608,z2,z3,z4,z5]),(0,[z1,z2,z3,z609,z25,z4,z5])],[(0,[z12,z1,z2,z118,z3,z4,z5]),(0,[z1,z2,z3,z25,z93,z4,z5]),(0,[z610,z6,z1,z2,z3,z4,z5]),(1,[z171,z1,z2,z3,z4,z5])],[(0,[z6,z1,z2,z3,z4,z5,z437])],[(0,[z80,z6,z1,z2,z178,z4,z5]),(0,[z256,z6,z1,z2,z3,z4,z38])],[(0,[z6,z1,z540,z2,z3,z4,z5]),(0,[z56,z1,z2,z3,z4,z5,z15]),(0,[z8,z6,z1,z2,z3,z4,z66]),(0,[z6,z1,z2,z3,z4,z5,z357]),(0,[z56,z6,z1,z2,z10,z3,z5]),(0,[z6,z1,z2,z611,z3,z4,z5])],[(0,[z202,z12,z1,z2,z3,z4,z5]),(0,[z28,z1,z2,z3,z4,z5,z15]),(0,[z6,z1,z2,z3,z4,z612,z5])],[(0,[z26,z1,z2,z3,z4,z5,z122]),(1,[z133,z1,z2,z3,z4,z5]),(0,[z6,z229,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z15,z48]),(0,[z24,z6,z1,z2,z3,z4,z38])],[(0,[z6,z92,z1,z2,z3,z4,z5]),(1,[z210,z1,z2,z3,z4,z5])],[(0,[z1,z2,z111,z3,z25,z4,z5]),(0,[z6,z1,z2,z3,z4,z613,z5]),(0,[z26,z1,z2,z111,z3,z4,z5]),(0,[z1,z2,z3,z289,z4,z119,z5]),(0,[z6,z1,z2,z3,z4,z5,z614])],[(0,[z1,z42,z2,z3,z114,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z615])]],
   [[(0,[z6,z1,z2,z616,z3,z4,z5]),(0,[z112,z1,z2,z3,z25,z4,z5]),(1,[z1,z2,z3,z25,z4,z66]),(0,[z1,z2,z3,z25,z4,z119,z5]),(0,[z6,z1,z2,z617,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z618]),(0,[z6,z1,z2,z3,z4,z5,z619])],[(0,[z620,z6,z1,z2,z3,z4,z5]),(0,[z19,z6,z42,z2,z3,z4,z5]),(0,[z1,z42,z2,z118,z3,z4,z5]),(0,[z45,z1,z88,z2,z3,z4,z5]),(0,[z6,z1,z2,z621,z3,z4,z5]),(0,[z1,z2,z3,z25,z4,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z522]),(0,[z6,z1,z622,z2,z3,z4,z5]),(0,[z623,z6,z1,z2,z3,z4,z5]),(0,[z269,z6,z1,z2,z3,z4,z38]),(0,[z6,z1,z2,z3,z4,z624,z5])],[(0,[z80,z1,z42,z2,z3,z4,z5]),(0,[z80,z6,z1,z2,z3,z132,z5]),(0,[z6,z625,z1,z2,z3,z4,z5])],[(0,[z6,z1,z577,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z311]),(1,[z6,z1,z425,z3,z4,z5]),(0,[z147,z6,z1,z2,z3,z4,z5])],[(0,[z6,z1,z2,z3,z626,z4,z5]),(0,[z73,z1,z2,z3,z25,z4,z5]),(0,[z74,z1,z2,z3,z25,z4,z5]),(1,[z1,z32,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z38,z40]),(1,[z6,z1,z52,z53,z4,z5])],[(0,[z35,z1,z42,z2,z3,z4,z5]),(0,[z12,z1,z42,z2,z3,z4,z5]),(0,[z12,z1,z209,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z627,z5]),(0,[z6,z1,z2,z3,z628,z4,z5])],[(0,[z41,z1,z42,z2,z3,z4,z5]),(0,[z6,z1,z77,z3,z221,z4,z5]),(0,[z6,z1,z629,z2,z3,z4,z5])],[(1,[z80,z6,z55,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z343])],[(0,[z45,z1,z2,z3,z604,z4,z5]),(0,[z630,z6,z1,z2,z3,z4,z5]),(0,[z12,z86,z1,z2,z3,z4,z5]),(0,[z631,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z416])],[(0,[z19,z26,z1,z2,z3,z4,z5]),(1,[z1,z42,z2,z3,z4,z38]),(0,[z6,z1,z632,z2,z3,z4,z5])],[(0,[z367,z26,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z10,z3,z49,z5]),(0,[z129,z6,z1,z2,z3,z4,z66]),(0,[z6,z1,z2,z3,z93,z4,z66])],[(0,[z1,z2,z3,z4,z5,z475,z15]),(1,[z6,z1,z2,z388,z4,z5]),(0,[z633,z6,z1,z2,z3,z4,z5])],[(0,[z634,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z635]),(0,[z636,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z637,z4,z5]),(0,[z6,z1,z2,z50,z3,z69,z5])],[(1,[z45,z1,z2,z3,z4,z66]),(0,[z6,z1,z2,z3,z4,z13,z38]),(0,[z1,z2,z3,z25,z4,z569,z5]),(0,[z1,z2,z3,z4,z5,z15,z38]),(0,[z6,z1,z2,z638,z3,z4,z5])],[(0,[z45,z1,z2,z3,z4,z116,z5]),(0,[z639,z6,z1,z2,z3,z4,z5]),(0,[z26,z1,z2,z55,z3,z4,z5]),(0,[z302,z1,z2,z3,z4,z119,z5]),(0,[z411,z6,z1,z2,z3,z4,z119])],[(0,[z6,z1,z2,z3,z282,z4,z5]),(0,[z138,z6,z1,z2,z3,z4,z5])]],
   [[(0,[z1,z42,z42,z2,z3,z4,z5]),(0,[z1,z42,z209,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z272,z4,z5]),(0,[z1,z2,z3,z11,z4,z5,z15])],[(0,[z6,z1,z2,z65,z3,z4,z5]),(1,[z6,z1,z62,z3,z4,z5])],[(1,[z6,z1,z2,z3,z4,z5]),(0,[z6,z14,z1,z2,z3,z4,z109])],[(0,[z45,z1,z2,z3,z68,z4,z5]),(0,[z467,z6,z1,z2,z3,z4,z5]),(0,[z12,z1,z2,z53,z3,z4,z5]),(0,[z6,z1,z2,z640,z3,z4,z5]),(1,[z490,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z641,z3,z4,z5])],[(0,[z642,z6,z1,z2,z3,z4,z5]),(0,[z6,z643,z1,z2,z3,z4,z5]),(0,[z1,z2,z50,z3,z4,z5,z15]),(0,[z26,z1,z2,z3,z4,z17,z5]),(0,[z6,z1,z2,z3,z4,z119,z66])],[(0,[z6,z1,z2,z3,z644,z4,z5]),(0,[z86,z6,z1,z99,z3,z4,z5])],[(0,[z459,z12,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z645,z4,z5]),(0,[z56,z6,z1,z2,z50,z4,z5]),(0,[z646,z6,z1,z2,z3,z4,z5]),(0,[z56,z6,z1,z2,z10,z4,z5])],[(1,[z1,z2,z3,z91,z4,z5]),(0,[z26,z1,z2,z3,z4,z176,z5]),(0,[z8,z6,z2,z3,z4,z49,z5])],[(0,[z1,z2,z3,z25,z4,z572,z5]),(0,[z647,z6,z1,z2,z3,z4,z5])],[],[(0,[z6,z1,z648,z2,z3,z4,z5]),(0,[z45,z1,z2,z3,z4,z94,z5]),(0,[z199,z6,z1,z2,z3,z4,z66]),(0,[z39,z6,z1,z2,z3,z4,z38]),(0,[z6,z1,z2,z50,z3,z4,z38]),(0,[z6,z1,z2,z10,z3,z4,z38])],[],[(0,[z649,z6,z1,z2,z3,z4,z5])],[(0,[z45,z1,z2,z3,z25,z4,z5]),(0,[z86,z6,z1,z2,z3,z93,z4]),(0,[z6,z650,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z15,z15]),(1,[z6,z1,z327,z3,z4,z5]),(0,[z490,z6,z1,z2,z3,z4,z5]),(0,[z651,z6,z1,z2,z3,z4,z5]),(0,[z76,z6,z1,z2,z3,z4,z5])],[(0,[z45,z74,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z3,z4,z5]),(0,[z80,z26,z1,z2,z3,z4,z5]),(0,[z56,z6,z1,z2,z3,z4,z66]),(0,[z6,z1,z2,z3,z4,z652,z5]),(0,[z653,z6,z1,z2,z3,z4,z5]),(0,[z147,z76,z1,z2,z3,z4,z5])]],
   [[],[(0,[z37,z26,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z66,z38]),(0,[z1,z2,z3,z153,z93,z4,z5])],[(0,[z12,z26,z1,z2,z3,z4,z5]),(0,[z1,z2,z55,z3,z4,z5,z15]),(0,[z26,z1,z77,z2,z3,z4,z5]),(0,[z141,z6,z1,z2,z3,z4,z38])],[(1,[z127,z1,z88,z3,z4,z5]),(0,[z6,z1,z2,z3,z654,z4,z5]),(0,[z6,z1,z2,z655,z3,z4,z5]),(0,[z6,z1,z2,z65,z3,z4,z18])],[(0,[z79,z45,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z656,z3,z4,z5]),(0,[z41,z6,z1,z2,z3,z93,z4])],[(0,[z12,z1,z2,z3,z4,z96,z5]),(0,[z605,z1,z2,z3,z4,z5,z15]),(0,[z6,z1,z2,z3,z4,z5,z657]),(0,[z6,z1,z2,z3,z221,z4,z38]),(0,[z147,z6,z1,z2,z3,z4,z96])],[(0,[z8,z1,z42,z2,z3,z4,z5]),(0,[z6,z92,z1,z2,z3,z4,z108]),(0,[z159,z1,z2,z3,z25,z4,z5]),(1,[z26,z1,z2,z3,z4,z38]),(0,[z6,z1,z2,z3,z491,z4,z5]),(0,[z39,z6,z1,z2,z3,z114,z5])],[(0,[z80,z12,z1,z2,z3,z4,z5]),(1,[z232,z1,z2,z3,z4,z5])],[(1,[z1,z139,z2,z3,z4,z5]),(0,[z147,z86,z6,z1,z2,z3,z4])],[(0,[z256,z45,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z100])],[(0,[z12,z12,z1,z2,z3,z4,z5]),(0,[z147,z278,z1,z2,z3,z4,z5])],[(0,[z658,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z659,z5])],[(0,[z6,z1,z2,z306,z3,z4,z5])],[(0,[z24,z45,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z309])],[(0,[z79,z35,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z660,z5]),(1,[z12,z1,z2,z3,z4,z38]),(0,[z661,z6,z1,z2,z3,z4,z5])],[(1,[z543,z1,z2,z3,z4,z5]),(0,[z127,z6,z1,z88,z3,z4,z5]),(0,[z26,z6,z1,z2,z3,z4,z5]),(0,[z662,z6,z1,z2,z3,z4,z5])]],
   [[(0,[z26,z1,z2,z3,z221,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z562])],[(0,[z26,z112,z1,z2,z3,z4,z5]),(0,[z141,z431,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z663,z5])],[(0,[z1,z2,z3,z25,z4,z421,z5]),(0,[z129,z6,z1,z2,z53,z4,z5])],[],[(0,[z6,z1,z2,z3,z4,z5,z664]),(0,[z6,z665,z1,z2,z3,z4,z5]),(0,[z666,z6,z1,z2,z3,z4,z5]),(0,[z87,z6,z1,z2,z3,z4,z5]),(0,[z210,z1,z2,z3,z4,z116,z5])],[(0,[z1,z648,z42,z2,z3,z4,z5]),(0,[z56,z6,z1,z2,z111,z4,z5]),(0,[z6,z28,z1,z2,z3,z49,z5])],[(0,[z6,z1,z2,z3,z4,z108,z5]),(0,[z6,z575,z1,z2,z3,z4,z5])],[(0,[z129,z1,z42,z2,z3,z4,z5]),(1,[z26,z1,z2,z3,z4,z15]),(0,[z325,z1,z2,z3,z4,z69,z5])],[(0,[z6,z1,z2,z667,z3,z4,z5]),(0,[z147,z1,z2,z3,z4,z5,z15]),(0,[z6,z1,z2,z3,z668,z4,z5]),(0,[z147,z6,z1,z146,z3,z4,z5])],[(0,[z578,z6,z1,z2,z3,z4,z5]),(0,[z6,z531,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z609,z4,z5]),(0,[z6,z1,z2,z3,z669,z4,z5]),(0,[z670,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z116,z5]),(1,[z278,z1,z2,z3,z4,z5])],[(0,[z543,z1,z42,z2,z3,z4,z5]),(0,[z501,z12,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z671,z3,z4,z5]),(0,[z6,z672,z1,z2,z3,z4,z5])],[(0,[z12,z39,z1,z2,z3,z4,z5]),(0,[z673,z6,z1,z2,z3,z4,z5])],[(0,[z6,z112,z1,z2,z3,z4,z391]),(1,[z6,z1,z2,z3,z4,z413]),(0,[z674,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z517])],[(0,[z6,z1,z52,z77,z3,z4,z5])],[(0,[z39,z1,z2,z3,z25,z4,z5]),(0,[z675,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z68,z4,z5])],[(0,[z1,z42,z2,z3,z93,z4,z5]),(0,[z208,z1,z2,z3,z25,z4,z5])]],
   [[],[(0,[z6,z1,z2,z111,z3,z4,z5])],[(0,[z86,z1,z42,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z51,z5]),(0,[z6,z1,z53,z3,z221,z4,z5])],[(0,[z6,z1,z2,z3,z4,z5,z676]),(0,[z446,z26,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z677,z4,z5]),(0,[z6,z159,z1,z2,z3,z4,z38])],[(1,[z6,z1,z2,z3,z4,z63]),(0,[z6,z1,z88,z2,z3,z4,z66]),(1,[z6,z1,z2,z3,z4,z461]),(0,[z6,z14,z1,z2,z3,z4,z66]),(0,[z6,z1,z678,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z11,z119,z5])],[(0,[z6,z1,z2,z3,z4,z94,z5]),(0,[z6,z1,z2,z3,z11,z4,z5]),(0,[z6,z1,z2,z3,z4,z49,z38]),(0,[z6,z28,z1,z2,z3,z4,z38])],[(0,[z299,z6,z1,z2,z3,z4,z5]),(0,[z1,z2,z44,z3,z4,z5,z15]),(0,[z6,z346,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z347,z5]),(0,[z1,z2,z3,z4,z5,z15,z40]),(1,[z6,z28,z2,z3,z4,z38]),(0,[z129,z6,z1,z2,z221,z4,z5]),(0,[z6,z1,z2,z3,z679,z4,z5])],[(0,[z199,z1,z42,z2,z3,z4,z5]),(1,[z1,z2,z3,z4,z5,z15]),(0,[z6,z1,z2,z3,z4,z69,z38])],[(0,[z6,z1,z2,z3,z25,z4,z5]),(0,[z1,z2,z3,z25,z4,z5,z522]),(0,[z141,z110,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z114,z49,z5])],[(0,[z1,z2,z3,z25,z4,z5,z18]),(0,[z6,z1,z2,z3,z4,z680,z5])],[(0,[z45,z1,z52,z2,z3,z4,z5]),(0,[z6,z1,z681,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z682,z5])],[(0,[z39,z45,z1,z2,z3,z4,z5]),(0,[z8,z12,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z318,z4,z5]),(0,[z6,z1,z2,z3,z4,z683,z5])],[(0,[z56,z1,z42,z2,z3,z4,z5]),(0,[z45,z1,z2,z3,z91,z4,z5]),(0,[z6,z1,z2,z68,z221,z4,z5]),(1,[z6,z1,z2,z310,z4,z5])],[(0,[z684,z6,z1,z2,z3,z4,z5]),(0,[z28,z1,z42,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z685,z5]),(0,[z6,z1,z2,z388,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z686,z5]),(0,[z687,z6,z1,z2,z3,z4,z5]),(1,[z250,z1,z2,z3,z4,z5])],[(0,[z6,z1,z2,z3,z4,z688,z5]),(0,[z6,z1,z2,z3,z689,z4,z5]),(0,[z368,z6,z1,z2,z3,z4,z38])],[(1,[z45,z42,z2,z3,z4,z5]),(0,[z45,z1,z99,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z46,z4,z5])]],
   [[(0,[z690,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z691,z3,z4,z5]),(0,[z692,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z693,z2,z3,z4,z5]),(0,[z694,z6,z1,z2,z3,z4,z5])],[(0,[z695,z6,z1,z2,z3,z4,z5]),(0,[z1,z2,z326,z3,z25,z4,z5]),(0,[z6,z1,z125,z2,z3,z4,z5]),(0,[z24,z575,z1,z2,z3,z4,z5])],[(0,[z26,z1,z2,z3,z4,z69,z5])],[(0,[z141,z45,z1,z2,z3,z4,z5]),(0,[z127,z6,z1,z2,z3,z4,z38]),(0,[z26,z1,z2,z3,z4,z5,z38]),(0,[z6,z1,z2,z3,z4,z5,z696])],[(0,[z313,z45,z1,z2,z3,z4,z5]),(0,[z697,z6,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z221,z25,z4,z5]),(0,[z1,z2,z3,z4,z116,z5,z15]),(0,[z129,z26,z1,z2,z3,z4,z5]),(0,[z698,z6,z1,z2,z3,z4,z5])],[],[(0,[z699,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z516,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z437,z15]),(0,[z6,z1,z2,z700,z3,z4,z5])],[(0,[z1,z2,z514,z3,z25,z4,z5]),(1,[z41,z6,z1,z2,z4,z18])],[(0,[z6,z92,z1,z2,z3,z4,z66]),(0,[z35,z73,z1,z2,z3,z4,z5]),(0,[z12,z73,z1,z2,z3,z4,z5]),(0,[z6,z112,z2,z111,z3,z4,z5]),(0,[z6,z1,z2,z3,z114,z4,z38])],[(0,[z45,z1,z2,z111,z3,z4,z5]),(0,[z6,z1,z2,z3,z701,z4,z5])],[(0,[z79,z6,z1,z118,z3,z4,z5]),(0,[z79,z1,z2,z3,z25,z4,z5]),(0,[z6,z1,z2,z118,z3,z4,z38]),(0,[z6,z1,z2,z702,z3,z4,z5]),(1,[z6,z1,z2,z3,z4,z7]),(0,[z6,z1,z2,z3,z4,z66,z40])],[(0,[z127,z1,z88,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z703,z5]),(0,[z26,z1,z2,z3,z4,z13,z5]),(0,[z6,z1,z2,z3,z4,z5,z704]),(0,[z6,z1,z2,z3,z4,z66,z217])],[(0,[z12,z1,z2,z44,z3,z4,z5]),(0,[z705,z6,z1,z2,z3,z4,z5])],[(0,[z45,z1,z2,z3,z11,z4,z5]),(0,[z1,z52,z2,z3,z25,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z453]),(1,[z6,z1,z99,z3,z4,z116])],[(0,[z6,z1,z2,z3,z706,z4,z5]),(0,[z147,z6,z1,z2,z3,z4,z66])],[(1,[z256,z1,z2,z3,z4,z5]),(0,[z86,z26,z1,z2,z3,z4,z5]),(1,[z141,z6,z2,z68,z4,z5]),(0,[z6,z1,z468,z2,z3,z4,z5])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z79,z1,z118,z3,z4,z66]),(0,[z6,z1,z365,z3,z4,z416]),(0,[z1,z366,z2,z3,z4,z66]),(0,[z106,z325,z1,z2,z3,z4])],[(0,[z6,z1,z2,z3,z4,z707]),(0,[z6,z1,z708,z3,z4,z5]),(0,[z709,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z710]),(0,[z6,z1,z2,z65,z4,z216])],[(0,[z1,z2,z3,z4,z711,z5]),(0,[z712,z1,z2,z3,z4,z5]),(0,[z6,z1,z713,z3,z4,z5]),(0,[z714,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z715,z5]),(0,[z6,z1,z2,z3,z4,z716]),(0,[z76,z261,z2,z3,z4,z5])],[(0,[z141,z42,z2,z68,z4,z5]),(0,[z1,z717,z2,z3,z4,z5])],[(0,[z1,z2,z3,z718,z4,z5]),(0,[z45,z1,z2,z3,z4,z447]),(0,[z12,z1,z2,z3,z4,z158]),(0,[z24,z26,z2,z3,z4,z38]),(0,[z6,z2,z3,z119,z49,z38]),(0,[z1,z2,z3,z4,z5,z719]),(0,[z1,z720,z2,z3,z4,z5])],[(0,[z6,z1,z2,z3,z4,z38]),(0,[z1,z2,z3,z25,z4,z214]),(0,[z721,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z722])],[(0,[z12,z1,z2,z3,z25,z66]),(0,[z723,z1,z2,z3,z4,z5]),(0,[z234,z1,z2,z178,z4,z5]),(0,[z6,z1,z2,z3,z4,z724]),(0,[z490,z1,z2,z3,z4,z38]),(0,[z147,z6,z164,z2,z3,z122])],[(0,[z1,z125,z3,z4,z5,z15]),(0,[z725,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z726,z4,z5]),(0,[z6,z1,z2,z4,z727,z18])],[(0,[z45,z1,z468,z3,z4,z5]),(0,[z728,z1,z2,z3,z4,z5]),(0,[z45,z1,z2,z3,z93,z96]),(0,[z376,z1,z2,z3,z4,z66]),(0,[z729,z1,z2,z3,z4,z5]),(0,[z6,z261,z2,z3,z4,z96])],[(0,[z730,z1,z2,z3,z4,z5]),(0,[z731,z6,z1,z2,z3,z4]),(0,[z6,z227,z2,z3,z11,z5]),(0,[z130,z1,z2,z3,z4,z66])],[(0,[z1,z2,z3,z4,z5,z732]),(0,[z36,z1,z2,z3,z25,z5]),(0,[z733,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z734,z4,z38]),(0,[z735,z1,z2,z3,z4,z66])],[(0,[z368,z1,z2,z3,z4,z15]),(0,[z736,z6,z1,z2,z3,z4]),(0,[z6,z1,z2,z275,z4,z66]),(0,[z41,z6,z1,z2,z286,z4])],[(0,[z6,z1,z2,z3,z4,z737]),(0,[z6,z1,z2,z3,z4,z738]),(0,[z417,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z739])],[(0,[z1,z2,z3,z91,z11,z5]),(0,[z740,z1,z2,z3,z4,z5]),(0,[z2,z3,z25,z4,z421,z38]),(0,[z6,z1,z2,z3,z4,z741]),(0,[z1,z2,z3,z742,z4,z5]),(0,[z743,z1,z2,z3,z4,z5])],[(0,[z19,z59,z2,z3,z4,z5]),(0,[z6,z1,z2,z744,z4,z5]),(1,[z1,z2,z745,z4,z5]),(0,[z12,z1,z2,z3,z132,z5]),(0,[z746,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z421,z5]),(0,[z747,z1,z2,z3,z4,z5]),(0,[z748,z1,z2,z3,z4,z5]),(0,[z76,z1,z2,z275,z4,z5])]],
   [[(0,[z6,z1,z2,z3,z4,z749]),(0,[z6,z1,z2,z3,z750,z5]),(0,[z1,z751,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z752,z5]),(0,[z6,z1,z2,z3,z4,z753]),(0,[z1,z2,z3,z4,z754,z5]),(0,[z28,z2,z3,z25,z4,z38]),(0,[z1,z2,z3,z4,z15,z696]),(0,[z6,z1,z327,z3,z4,z38]),(0,[z755,z1,z2,z3,z4,z5])],[(0,[z428,z1,z2,z3,z4,z5]),(0,[z543,z1,z2,z3,z49,z5]),(0,[z1,z756,z2,z3,z4,z5]),(0,[z45,z1,z2,z3,z4,z214]),(0,[z757,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z758]),(0,[z28,z2,z3,z11,z5,z15]),(0,[z6,z1,z2,z3,z4,z759]),(0,[z1,z2,z3,z4,z5,z760]),(0,[z761,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z212,z15]),(0,[z1,z2,z3,z25,z4,z179]),(0,[z1,z2,z3,z25,z4,z762]),(0,[z1,z2,z3,z4,z763,z5]),(0,[z764,z1,z2,z3,z4,z5])],[(0,[z6,z1,z2,z3,z4,z765]),(0,[z431,z1,z2,z3,z4,z5]),(0,[z411,z45,z1,z2,z3,z4]),(0,[z45,z1,z2,z3,z4,z499]),(0,[z766,z6,z1,z3,z4,z5]),(0,[z767,z1,z2,z3,z4,z5]),(0,[z1,z34,z2,z3,z4,z38]),(0,[z292,z6,z1,z3,z114,z5]),(0,[z1,z2,z3,z4,z5,z768])],[(0,[z1,z468,z3,z4,z5,z15]),(0,[z6,z1,z2,z310,z4,z182]),(0,[z1,z2,z3,z4,z9,z769]),(0,[z770,z1,z2,z3,z4,z5])],[(0,[z127,z1,z88,z3,z4,z38]),(0,[z12,z1,z2,z3,z4,z771]),(0,[z1,z2,z3,z4,z772,z5]),(0,[z1,z2,z3,z4,z5,z773]),(0,[z1,z427,z2,z3,z4,z7]),(0,[z774,z6,z1,z2,z3,z4]),(0,[z6,z1,z2,z286,z4,z66])],[(0,[z12,z164,z2,z3,z4,z5]),(0,[z6,z1,z468,z339,z4,z5])],[(0,[z1,z2,z3,z4,z5,z775]),(0,[z1,z2,z3,z4,z5,z776]),(0,[z1,z2,z3,z4,z5,z777])],[(0,[z1,z395,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z778]),(0,[z1,z2,z3,z4,z15,z167]),(0,[z1,z2,z3,z4,z235,z66])],[(0,[z313,z1,z2,z3,z4,z317]),(0,[z779,z1,z2,z3,z4,z5]),(0,[z6,z14,z77,z3,z4,z109]),(0,[z6,z1,z2,z111,z145,z5]),(0,[z780,z1,z2,z3,z4,z5]),(0,[z232,z1,z2,z3,z4,z38]),(0,[z86,z6,z1,z3,z4,z781]),(0,[z782,z1,z2,z3,z4,z5]),(0,[z76,z1,z2,z286,z4,z5])],[(0,[z1,z2,z3,z4,z5,z437]),(0,[z233,z1,z2,z3,z4,z5]),(0,[z1,z139,z2,z3,z4,z38]),(0,[z783,z1,z2,z3,z4,z5]),(0,[z6,z261,z146,z3,z4,z5])],[(0,[z784,z42,z2,z3,z4,z5]),(0,[z45,z341,z2,z3,z4,z5]),(0,[z26,z1,z2,z3,z4,z66]),(0,[z1,z2,z3,z4,z5,z785]),(0,[z8,z6,z2,z3,z49,z66]),(0,[z786,z1,z2,z3,z4,z5])],[],[(0,[z2,z3,z4,z437,z15,z38]),(0,[z6,z1,z2,z3,z4,z787])],[(0,[z788,z1,z2,z3,z4,z5]),(0,[z1,z789,z2,z3,z4,z5]),(0,[z605,z42,z2,z3,z4,z5]),(0,[z229,z1,z2,z3,z4,z5]),(0,[z12,z1,z2,z3,z248,z5]),(0,[z790,z2,z3,z25,z4,z5]),(0,[z1,z791,z2,z3,z4,z5]),(0,[z6,z1,z792,z221,z4,z5])]],
   [[(0,[z1,z648,z2,z3,z25,z5]),(0,[z256,z1,z2,z3,z4,z15]),(0,[z26,z1,z2,z3,z4,z635]),(0,[z1,z2,z3,z4,z158,z15])],[(0,[z1,z308,z88,z3,z4,z5]),(0,[z1,z62,z3,z4,z5,z15]),(0,[z129,z130,z1,z221,z4,z5]),(0,[z1,z2,z3,z793,z4,z5]),(0,[z794,z1,z2,z3,z4,z5])],[(0,[z1,z42,z2,z178,z4,z5]),(0,[z543,z1,z2,z3,z4,z38]),(0,[z199,z1,z2,z3,z4,z317]),(0,[z1,z2,z3,z4,z5,z795]),(0,[z796,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z178,z132,z5])],[(0,[z1,z42,z2,z3,z4,z9]),(0,[z6,z1,z2,z3,z4,z797]),(0,[z325,z1,z2,z3,z4,z66]),(0,[z798,z1,z2,z3,z4,z5]),(0,[z799,z1,z2,z3,z4,z5])],[(0,[z800,z1,z2,z3,z4,z5]),(0,[z6,z1,z209,z3,z119,z66]),(0,[z106,z801,z1,z2,z3,z4])],[(0,[z6,z1,z2,z3,z4,z802]),(0,[z1,z2,z3,z4,z5,z803]),(0,[z45,z1,z2,z3,z4,z461]),(0,[z1,z2,z3,z4,z5,z522]),(0,[z1,z2,z286,z25,z4,z5]),(0,[z1,z2,z3,z4,z242,z15]),(0,[z26,z1,z804,z3,z4,z5]),(0,[z268,z1,z2,z3,z4,z66])],[(0,[z1,z805,z2,z3,z4,z5]),(0,[z455,z42,z2,z3,z4,z5]),(0,[z45,z504,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z806]),(0,[z1,z2,z3,z170,z5,z122]),(0,[z81,z6,z1,z2,z4,z97]),(0,[z807,z1,z2,z3,z4,z82])],[(0,[z6,z1,z2,z3,z4,z211]),(0,[z45,z1,z425,z3,z4,z5]),(0,[z1,z2,z3,z25,z551,z5]),(0,[z1,z2,z3,z93,z4,z522]),(0,[z1,z2,z310,z4,z5,z15]),(0,[z431,z1,z2,z3,z4,z51])],[(0,[z387,z2,z3,z25,z4,z38]),(0,[z808,z6,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z809])],[(0,[z810,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z811]),(0,[z1,z427,z2,z3,z4,z66]),(0,[z6,z28,z2,z3,z49,z38]),(0,[z226,z1,z2,z3,z4,z214]),(0,[z812,z1,z2,z3,z4,z5]),(0,[z813,z1,z2,z3,z4,z5])],[(0,[z330,z1,z2,z46,z4,z5])],[(0,[z110,z1,z2,z3,z4,z5]),(0,[z35,z1,z2,z745,z4,z5]),(0,[z1,z2,z3,z4,z158,z814]),(0,[z556,z6,z2,z3,z4,z38])],[(0,[z1,z42,z2,z3,z132,z5]),(0,[z1,z2,z3,z815,z4,z5]),(0,[z6,z1,z816,z3,z4,z5]),(0,[z6,z2,z3,z69,z49,z38]),(0,[z6,z28,z2,z3,z817,z5]),(0,[z368,z1,z2,z3,z4,z48]),(0,[z278,z1,z2,z3,z4,z38])],[(0,[z1,z818,z2,z3,z4,z5]),(0,[z45,z92,z2,z3,z4,z499]),(0,[z819,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z820]),(0,[z6,z1,z821,z3,z4,z5]),(0,[z6,z650,z2,z3,z11,z5]),(0,[z822,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z745,z4,z5]),(0,[z12,z823,z2,z3,z4,z5]),(0,[z824,z1,z2,z3,z4,z38]),(0,[z177,z1,z2,z3,z4,z461]),(0,[z133,z1,z2,z339,z4,z5]),(0,[z825,z1,z2,z3,z4,z214]),(0,[z826,z1,z2,z3,z4,z5]),(0,[z24,z6,z2,z3,z4,z827])],[(0,[z256,z1,z2,z3,z4,z445]),(0,[z45,z1,z2,z388,z4,z5]),(0,[z45,z538,z2,z3,z4,z5]),(0,[z1,z59,z2,z3,z4,z48]),(0,[z39,z6,z1,z3,z750,z5])]],
   [[(0,[z6,z139,z2,z3,z4,z38]),(0,[z80,z55,z3,z4,z5,z15]),(0,[z26,z1,z2,z3,z120,z5]),(0,[z6,z1,z2,z828,z4,z5]),(0,[z6,z1,z2,z3,z4,z829]),(0,[z6,z1,z2,z65,z286,z4])],[(0,[z1,z42,z2,z3,z145,z5]),(0,[z42,z2,z3,z4,z305,z5]),(0,[z35,z1,z2,z272,z4,z5]),(0,[z26,z1,z2,z3,z4,z82]),(0,[z87,z1,z2,z3,z4,z66]),(0,[z6,z1,z2,z645,z69,z5]),(0,[z106,z6,z1,z2,z65,z4]),(0,[z147,z6,z1,z2,z275,z122])],[(0,[z6,z1,z2,z3,z4,z830]),(0,[z831,z1,z2,z3,z4,z5]),(0,[z6,z1,z3,z750,z119,z5])],[(0,[z159,z42,z2,z3,z4,z66]),(0,[z12,z346,z2,z3,z4,z38]),(0,[z1,z832,z2,z3,z4,z5]),(0,[z833,z1,z2,z25,z4,z5]),(0,[z834,z1,z2,z3,z4,z5]),(0,[z730,z1,z2,z3,z4,z413]),(0,[z6,z1,z3,z750,z4,z5]),(0,[z6,z1,z146,z286,z4,z5])],[(0,[z6,z1,z2,z3,z4,z835]),(0,[z1,z2,z3,z4,z66,z48]),(0,[z79,z1,z479,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z836])],[(0,[z12,z1,z837,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z838])],[(0,[z45,z1,z2,z3,z4,z5]),(0,[z208,z1,z118,z3,z4,z5]),(0,[z268,z1,z2,z3,z4,z109]),(0,[z839,z1,z2,z3,z4,z5]),(0,[z6,z1,z425,z339,z4,z5]),(0,[z6,z2,z3,z4,z156,z38]),(0,[z840,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z792,z4,z5]),(0,[z841,z1,z2,z3,z4,z5]),(0,[z842,z1,z2,z3,z4,z5]),(0,[z843,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z270,z15]),(1,[z6,z1,z2,z4,z727])],[(0,[z1,z42,z2,z275,z4,z5]),(0,[z844,z1,z2,z3,z4,z5])],[(0,[z41,z1,z42,z2,z4,z18]),(0,[z6,z1,z3,z845,z4,z5]),(0,[z26,z1,z2,z3,z4,z846]),(0,[z26,z1,z2,z3,z4,z657]),(0,[z6,z159,z2,z3,z4,z66]),(0,[z6,z2,z3,z267,z4,z38]),(0,[z269,z6,z1,z3,z4,z40]),(0,[z6,z237,z2,z3,z4,z38])],[(0,[z1,z540,z2,z224,z4,z5]),(0,[z1,z2,z3,z25,z4,z447]),(0,[z847,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z848]),(0,[z8,z348,z2,z3,z49,z5]),(0,[z240,z6,z1,z2,z3,z122]),(0,[z6,z1,z99,z3,z4,z659])],[(0,[z45,z1,z2,z3,z4,z7]),(0,[z129,z45,z1,z221,z4,z5]),(0,[z256,z484,z2,z3,z4,z5]),(0,[z6,z1,z849,z2,z3,z4])],[(0,[z493,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z850,z4,z5])],[(0,[z6,z1,z2,z3,z4,z851]),(0,[z1,z2,z3,z4,z391,z852]),(0,[z853,z1,z2,z3,z4,z5])],[(0,[z436,z1,z2,z3,z4,z5]),(0,[z404,z42,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z854]),(0,[z1,z2,z3,z25,z93,z96]),(0,[z1,z2,z3,z4,z5,z855]),(0,[z110,z1,z2,z3,z4,z51]),(0,[z1,z2,z3,z856,z4,z5])],[(0,[z857,z1,z2,z3,z4,z5]),(0,[z26,z1,z2,z178,z4,z5]),(0,[z1,z2,z3,z4,z5,z858]),(0,[z6,z1,z2,z310,z4,z38]),(0,[z256,z1,z2,z3,z4,z337]),(0,[z6,z1,z859,z3,z4,z38]),(0,[z6,z2,z3,z4,z860,z5]),(0,[z106,z1,z2,z3,z157,z4])]],
   [[(0,[z288,z1,z2,z3,z4,z66]),(0,[z123,z1,z2,z3,z170,z5]),(0,[z26,z1,z2,z3,z4,z9]),(0,[z348,z1,z2,z310,z4,z5]),(0,[z8,z6,z2,z3,z49,z9]),(0,[z250,z1,z2,z3,z4,z38])],[(0,[z202,z1,z2,z3,z91,z5]),(0,[z1,z2,z3,z4,z5,z852]),(0,[z1,z2,z3,z4,z5,z769]),(0,[z6,z1,z144,z3,z119,z5]),(0,[z6,z1,z2,z65,z4,z727]),(0,[z6,z164,z2,z275,z4,z5])],[(0,[z45,z42,z2,z3,z4,z38]),(0,[z45,z1,z327,z3,z4,z5]),(0,[z141,z2,z68,z25,z4,z5]),(0,[z861,z1,z2,z3,z4,z5]),(0,[z862,z1,z2,z3,z4,z5]),(0,[z431,z1,z125,z3,z4,z5]),(0,[z1,z2,z3,z4,z38,z863])],[(0,[z1,z42,z2,z286,z4,z5]),(0,[z86,z45,z1,z3,z4,z40]),(0,[z864,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z865,z5]),(0,[z866,z1,z2,z3,z4,z15]),(0,[z867,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z868])],[(0,[z26,z484,z2,z3,z4,z38]),(0,[z6,z1,z2,z339,z4,z5])],[(0,[z1,z2,z339,z4,z5,z15]),(0,[z869,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z870,z4,z5]),(0,[z871,z1,z2,z3,z4,z167]),(0,[z610,z6,z1,z2,z10,z5]),(0,[z1,z2,z3,z872,z4,z5])],[(0,[z1,z2,z44,z61,z4,z5]),(0,[z12,z1,z2,z178,z4,z5]),(0,[z873,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z874])],[(0,[z12,z1,z2,z3,z4,z9]),(0,[z1,z2,z875,z25,z4,z5])],[(0,[z348,z1,z2,z3,z4,z5]),(0,[z39,z45,z1,z3,z114,z5]),(0,[z1,z2,z616,z3,z25,z5]),(0,[z174,z59,z2,z3,z4,z5]),(0,[z26,z1,z2,z3,z132,z5]),(0,[z6,z1,z327,z3,z4,z179]),(0,[z6,z1,z2,z50,z69,z5]),(0,[z6,z1,z876,z3,z4,z5])],[(0,[z127,z1,z577,z3,z4,z5]),(0,[z1,z2,z3,z25,z4,z499]),(0,[z1,z2,z3,z491,z4,z5]),(0,[z877,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z4,z5,z878]),(0,[z6,z1,z2,z3,z4,z879])],[(0,[z26,z1,z2,z3,z4,z230]),(0,[z880,z1,z2,z3,z120,z5])],[(0,[z1,z2,z3,z4,z300,z15]),(0,[z6,z1,z2,z881,z4,z5]),(0,[z6,z14,z77,z3,z4,z66]),(0,[z6,z1,z3,z882,z4,z5]),(0,[z1,z2,z3,z883,z4,z5]),(0,[z6,z164,z2,z286,z4,z5])],[(0,[z1,z2,z3,z4,z109,z15]),(0,[z80,z6,z55,z3,z318,z5])],[(0,[z6,z1,z2,z3,z4,z884]),(0,[z1,z301,z2,z3,z4,z15]),(0,[z1,z2,z275,z4,z5,z15]),(0,[z26,z1,z2,z3,z145,z5])],[(0,[z45,z92,z2,z3,z4,z5]),(0,[z885,z6,z1,z2,z3,z4]),(0,[z411,z6,z1,z209,z3,z119])]],
   [[(0,[z6,z1,z2,z3,z4,z886]),(0,[z74,z1,z2,z3,z25,z5]),(0,[z1,z209,z3,z25,z119,z5]),(0,[z1,z887,z2,z3,z4,z5]),(0,[z6,z1,z3,z4,z5,z888])],[(0,[z1,z42,z209,z3,z119,z5]),(0,[z6,z1,z2,z889,z4,z5]),(0,[z1,z2,z3,z4,z5,z309]),(0,[z1,z59,z2,z3,z4,z15]),(0,[z6,z1,z2,z388,z318,z5]),(0,[z133,z1,z468,z3,z4,z5]),(0,[z24,z250,z2,z3,z4,z38]),(0,[z6,z2,z3,z205,z4,z38])],[(0,[z1,z42,z2,z3,z4,z167]),(0,[z1,z2,z3,z187,z4,z38]),(0,[z256,z1,z2,z3,z4,z38]),(0,[z890,z1,z2,z3,z4,z5]),(0,[z26,z164,z2,z3,z4,z5]),(0,[z1,z891,z2,z3,z4,z5]),(0,[z141,z6,z2,z68,z4,z38]),(0,[z825,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z892])],[(0,[z1,z2,z3,z93,z4,z309]),(0,[z0,z1,z2,z3,z4,z38])],[(0,[z35,z1,z2,z604,z4,z5]),(0,[z252,z1,z2,z46,z4,z5]),(0,[z6,z2,z3,z4,z49,z182]),(0,[z1,z2,z3,z893,z4,z5])],[(0,[z894,z1,z2,z3,z4,z5]),(0,[z26,z1,z2,z275,z4,z5]),(0,[z6,z59,z2,z3,z4,z38]),(0,[z6,z1,z2,z3,z4,z895])],[(0,[z45,z206,z2,z3,z4,z5]),(0,[z12,z1,z2,z3,z145,z5]),(0,[z1,z2,z3,z4,z66,z15]),(0,[z56,z1,z2,z10,z5,z15]),(0,[z896,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z897,z4,z5]),(0,[z6,z1,z102,z221,z4,z5])],[(0,[z12,z1,z2,z898,z4,z5]),(0,[z28,z2,z3,z25,z11,z5]),(0,[z367,z1,z383,z3,z4,z5]),(0,[z177,z1,z2,z3,z4,z66]),(0,[z6,z1,z2,z3,z4,z899]),(0,[z900,z1,z2,z3,z4,z5]),(0,[z28,z2,z3,z4,z38,z48])],[(0,[z12,z1,z2,z3,z91,z5]),(0,[z12,z901,z2,z3,z4,z5]),(0,[z39,z1,z3,z114,z5,z15]),(0,[z6,z1,z2,z3,z318,z5]),(0,[z902,z1,z2,z3,z4,z5])],[(0,[z1,z2,z50,z25,z69,z5]),(0,[z110,z1,z125,z3,z4,z5]),(0,[z1,z2,z3,z4,z903,z5])],[(0,[z575,z1,z2,z3,z4,z5]),(0,[z1,z2,z904,z3,z4,z5]),(0,[z1,z146,z3,z4,z5,z15]),(0,[z6,z1,z481,z53,z4,z5]),(0,[z905,z1,z2,z3,z4,z5]),(0,[z6,z2,z3,z4,z66,z38]),(0,[z6,z2,z3,z4,z215,z38])],[(0,[z19,z42,z2,z3,z4,z5]),(0,[z6,z1,z2,z906,z4,z5]),(0,[z1,z2,z3,z25,z4,z461]),(0,[z330,z1,z2,z326,z4,z5]),(0,[z1,z2,z3,z907,z4,z5]),(0,[z6,z1,z2,z3,z4,z908]),(0,[z909,z1,z2,z3,z318,z5]),(0,[z910,z1,z2,z3,z4,z5]),(0,[z6,z482,z2,z3,z4,z66]),(0,[z6,z1,z2,z3,z4,z911]),(0,[z147,z6,z1,z2,z3,z122])],[(0,[z912,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z913]),(0,[z1,z2,z3,z4,z5,z914]),(0,[z6,z1,z2,z3,z4,z915]),(0,[z1,z2,z3,z4,z5,z916])],[(0,[z444,z42,z2,z3,z4,z5]),(0,[z56,z1,z42,z2,z10,z5]),(0,[z12,z1,z2,z275,z4,z5]),(0,[z2,z3,z4,z49,z15,z38]),(0,[z299,z1,z27,z3,z4,z5]),(0,[z6,z2,z3,z4,z38,z392])],[(0,[z6,z1,z2,z3,z4,z917]),(0,[z6,z1,z2,z3,z4,z391])],[(0,[z106,z1,z42,z2,z3,z4]),(0,[z45,z1,z2,z3,z4,z108]),(0,[z6,z1,z2,z3,z918,z5]),(0,[z1,z919,z2,z3,z4,z5])]],
   [[(0,[z45,z1,z2,z3,z4,z413]),(0,[z1,z2,z3,z4,z5,z517]),(0,[z920,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z827]),(0,[z56,z6,z1,z2,z921,z5])],[(0,[z45,z139,z2,z3,z4,z5]),(0,[z256,z1,z2,z3,z4,z94]),(0,[z922,z6,z1,z2,z3,z4]),(0,[z923,z1,z2,z3,z4,z5])],[],[(0,[z377,z6,z2,z3,z49,z5]),(0,[z6,z625,z2,z3,z4,z66])],[(0,[z924,z1,z2,z3,z4,z5]),(0,[z925,z1,z2,z3,z4,z5]),(0,[z926,z1,z2,z3,z4,z5]),(0,[z256,z2,z3,z4,z66,z38]),(0,[z240,z6,z1,z2,z3,z207]),(0,[z76,z1,z2,z3,z4,z38]),(0,[z927,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z4,z17,z727])],[(0,[z1,z2,z3,z4,z5,z928]),(0,[z6,z1,z2,z875,z4,z5]),(0,[z288,z1,z2,z3,z4,z309]),(0,[z1,z2,z3,z4,z66,z929]),(0,[z6,z1,z930,z3,z4,z5]),(0,[z129,z6,z1,z221,z4,z5])],[(0,[z1,z931,z2,z3,z4,z5]),(0,[z1,z932,z2,z3,z4,z5]),(0,[z6,z933,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z934,z5]),(0,[z1,z2,z3,z132,z5,z15]),(0,[z935,z1,z2,z3,z4,z5]),(0,[z417,z1,z2,z3,z4,z66]),(0,[z936,z1,z2,z3,z4,z5])],[(0,[z45,z1,z2,z3,z4,z63]),(0,[z543,z1,z2,z3,z11,z5]),(0,[z12,z1,z2,z286,z4,z5]),(0,[z1,z2,z3,z4,z5,z937]),(0,[z6,z1,z468,z3,z4,z5]),(0,[z6,z1,z99,z146,z3,z4])],[(0,[z6,z1,z938,z3,z4,z5]),(0,[z12,z1,z2,z3,z176,z5]),(0,[z764,z1,z2,z3,z4,z51]),(0,[z56,z490,z1,z2,z10,z5])],[(0,[z45,z28,z2,z3,z4,z38]),(0,[z939,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z940]),(0,[z1,z2,z3,z4,z421,z66]),(0,[z1,z2,z3,z941,z4,z5]),(0,[z942,z1,z2,z3,z4,z5])],[(0,[z45,z1,z146,z3,z4,z5]),(0,[z6,z1,z2,z65,z4,z121])],[(0,[z1,z2,z3,z25,z4,z5]),(0,[z127,z1,z383,z3,z4,z5]),(0,[z943,z1,z2,z3,z4,z5]),(0,[z98,z1,z2,z3,z4,z38])],[(0,[z45,z28,z2,z3,z11,z5]),(0,[z944,z1,z2,z3,z4,z5]),(0,[z428,z1,z2,z3,z4,z66]),(0,[z86,z6,z1,z3,z4,z40]),(0,[z945,z1,z2,z3,z4,z5])],[(0,[z1,z88,z3,z4,z5,z475]),(0,[z1,z2,z745,z46,z4,z5]),(0,[z605,z6,z2,z3,z4,z38]),(0,[z1,z2,z3,z946,z4,z5]),(0,[z56,z6,z1,z2,z10,z38])],[(0,[z26,z1,z2,z3,z4,z167]),(0,[z411,z26,z1,z2,z3,z4]),(0,[z431,z1,z2,z3,z4,z66])]],
   [[(0,[z45,z1,z2,z310,z4,z5]),(0,[z1,z2,z3,z93,z96,z15]),(0,[z133,z1,z425,z3,z4,z5]),(0,[z6,z1,z2,z3,z418,z156])],[(0,[z1,z2,z3,z25,z4,z7]),(1,[z2,z3,z4,z437,z38]),(0,[z234,z1,z2,z3,z4,z38]),(0,[z6,z1,z2,z3,z4,z947])],[(0,[z14,z42,z77,z3,z4,z5]),(0,[z26,z1,z2,z3,z4,z396]),(0,[z6,z2,z948,z68,z4,z5]),(0,[z6,z1,z2,z3,z4,z214]),(0,[z949,z1,z2,z3,z4,z5])],[(0,[z12,z1,z2,z3,z198,z5]),(0,[z6,z1,z2,z3,z320,z357]),(0,[z39,z6,z1,z3,z114,z5]),(0,[z411,z950,z1,z2,z3,z4])],[(0,[z256,z1,z2,z3,z4,z211]),(0,[z19,z784,z2,z3,z4,z5]),(0,[z1,z395,z2,z3,z4,z66]),(0,[z1,z42,z2,z65,z4,z17]),(0,[z147,z45,z1,z2,z3,z122]),(0,[z376,z1,z2,z3,z5,z122]),(0,[z6,z1,z2,z3,z120,z38])],[(0,[z1,z2,z3,z4,z5,z951])],[(0,[z6,z1,z2,z3,z952,z5]),(0,[z12,z1,z953,z3,z4,z5]),(0,[z12,z1,z209,z3,z119,z5]),(0,[z954,z1,z2,z3,z4,z5]),(0,[z141,z431,z2,z68,z4,z5]),(0,[z6,z1,z125,z3,z4,z38]),(0,[z233,z1,z2,z3,z4,z66])],[(0,[z12,z1,z2,z3,z4,z167]),(0,[z24,z2,z3,z4,z15,z38]),(0,[z226,z1,z2,z3,z4,z413]),(0,[z131,z1,z2,z3,z4,z38]),(0,[z159,z366,z2,z3,z4,z66])],[(0,[z45,z92,z2,z3,z4,z108]),(0,[z1,z2,z3,z4,z929,z5]),(0,[z129,z1,z221,z4,z5,z15]),(0,[z1,z2,z3,z955,z4,z5]),(0,[z1,z2,z3,z956,z4,z5]),(0,[z957,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z958,z4,z5]),(0,[z1,z959,z2,z3,z4,z5])],[(0,[z1,z209,z3,z119,z5,z15]),(0,[z1,z99,z3,z4,z116,z15]),(0,[z1,z2,z3,z4,z5,z960])],[(0,[z177,z1,z2,z3,z4,z158]),(0,[z961,z1,z2,z3,z4,z5]),(0,[z229,z1,z2,z3,z4,z66]),(0,[z962,z1,z2,z3,z4,z5]),(0,[z6,z261,z99,z2,z3,z4]),(0,[z6,z261,z2,z275,z4,z5])],[(0,[z1,z88,z3,z4,z569,z5])],[(0,[z1,z2,z3,z4,z963,z5]),(0,[z6,z28,z2,z3,z4,z964]),(0,[z1,z965,z2,z3,z4,z5])],[(0,[z6,z1,z966,z3,z4,z5]),(0,[z199,z1,z2,z3,z4,z437]),(0,[z967,z1,z2,z3,z4,z5]),(0,[z6,z1,z146,z3,z4,z38]),(0,[z147,z6,z1,z2,z3,z968])],[(0,[z1,z2,z3,z4,z5,z969]),(0,[z12,z1,z2,z3,z4,z970]),(0,[z26,z1,z2,z3,z4,z58]),(0,[z6,z2,z3,z4,z49,z38])],[(0,[z133,z1,z2,z3,z4,z5]),(0,[z12,z1,z2,z3,z570,z5]),(0,[z6,z28,z2,z3,z11,z38]),(0,[z1,z2,z3,z4,z66,z217]),(0,[z147,z6,z261,z2,z3,z122])]],
   [[(0,[z6,z1,z2,z3,z971,z5]),(0,[z6,z1,z2,z3,z4,z762]),(0,[z972,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z153,z4,z38]),(0,[z1,z2,z3,z973,z4,z5]),(0,[z6,z1,z2,z3,z4,z179])],[(0,[z45,z1,z99,z3,z4,z116]),(0,[z147,z12,z1,z2,z3,z122]),(0,[z226,z28,z2,z3,z4,z38])],[(0,[z1,z648,z2,z3,z187,z5]),(0,[z1,z2,z3,z4,z214,z15]),(0,[z6,z1,z2,z3,z4,z974]),(0,[z1,z2,z3,z4,z109,z975]),(0,[z6,z1,z976,z3,z4,z5]),(0,[z1,z2,z3,z157,z4,z38]),(0,[z6,z1,z977,z3,z4,z38]),(0,[z978,z1,z2,z3,z4,z5])],[(0,[z45,z301,z2,z3,z4,z5]),(0,[z979,z1,z2,z3,z4,z5]),(0,[z1,z59,z2,z3,z4,z38]),(0,[z1,z980,z2,z3,z4,z5]),(0,[z431,z1,z2,z3,z120,z5]),(0,[z6,z1,z2,z565,z69,z5])],[(0,[z80,z6,z55,z388,z4,z5]),(0,[z812,z1,z2,z3,z4,z66]),(0,[z813,z1,z2,z3,z4,z66])],[(0,[z6,z1,z2,z3,z4,z981])],[(0,[z45,z59,z2,z3,z4,z5]),(0,[z159,z2,z3,z4,z421,z5]),(0,[z41,z1,z2,z25,z4,z18]),(0,[z1,z982,z2,z3,z4,z5]),(0,[z110,z1,z2,z3,z4,z66]),(0,[z6,z2,z3,z4,z214,z38]),(0,[z6,z1,z983,z3,z4,z5])],[(0,[z1,z984,z2,z3,z4,z5]),(0,[z985,z1,z2,z3,z4,z5]),(0,[z6,z1,z425,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z986]),(0,[z987,z1,z2,z3,z4,z5])],[(0,[z213,z1,z2,z180,z4,z5]),(0,[z256,z2,z3,z4,z49,z38]),(0,[z6,z1,z52,z53,z4,z5]),(0,[z988,z1,z2,z3,z4,z5])],[(0,[z1,z989,z2,z3,z4,z5]),(0,[z12,z1,z2,z990,z4,z5]),(0,[z6,z1,z2,z3,z4,z991]),(0,[z992,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z38,z993]),(0,[z1,z2,z3,z4,z5,z994]),(0,[z995,z1,z2,z3,z4,z5]),(0,[z6,z1,z99,z3,z4,z781]),(0,[z6,z1,z3,z4,z116,z781]),(0,[z996,z1,z2,z3,z4,z5])],[(0,[z6,z1,z2,z997,z4,z5]),(0,[z6,z1,z2,z3,z4,z998]),(0,[z6,z1,z2,z3,z318,z461]),(0,[z999,z1,z2,z3,z4,z5]),(0,[z141,z6,z2,z68,z4,z179]),(0,[z1,z2,z3,z1000,z4,z5])],[(0,[z1,z2,z3,z25,z223,z5]),(0,[z35,z1,z2,z57,z4,z5]),(0,[z1,z2,z3,z4,z1001,z5]),(0,[z1,z2,z3,z170,z4,z38]),(0,[z26,z261,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z1002])],[(0,[z1003,z1,z2,z3,z4,z5]),(0,[z45,z1,z2,z3,z4,z51]),(0,[z261,z2,z3,z25,z4,z5]),(0,[z1,z2,z3,z4,z5,z846]),(0,[z1004,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z38,z1005]),(0,[z1,z2,z3,z1006,z4,z5])],[(0,[z19,z42,z2,z3,z4,z63]),(0,[z1,z42,z2,z3,z4,z38]),(0,[z28,z34,z2,z3,z4,z38])],[(0,[z126,z1,z2,z3,z4,z38]),(0,[z411,z1,z2,z3,z289,z4]),(0,[z1,z2,z3,z1007,z4,z5]),(0,[z6,z1,z2,z3,z968,z122])],[(0,[z12,z1,z2,z3,z1008,z5]),(0,[z6,z1,z2,z388,z4,z5]),(0,[z6,z1,z2,z3,z4,z1009]),(0,[z6,z1,z2,z3,z4,z1010]),(0,[z6,z2,z294,z3,z4,z38]),(0,[z390,z6,z1,z2,z3,z453]),(0,[z1,z2,z3,z4,z5,z1011]),(0,[z56,z70,z1,z2,z10,z5])]],
   [[(0,[z226,z1,z2,z3,z4,z5]),(0,[z1012,z1,z2,z3,z4,z38]),(0,[z1013,z1,z2,z3,z4,z5])],[(0,[z45,z1,z2,z3,z4,z66]),(0,[z840,z1,z2,z3,z4,z66]),(0,[z1014,z1,z2,z3,z4,z5])],[(0,[z1015,z6,z1,z3,z4,z5]),(0,[z159,z2,z3,z4,z5,z437]),(0,[z1,z59,z2,z3,z4,z94]),(0,[z6,z1,z2,z3,z1016,z5]),(0,[z1017,z1,z2,z3,z4,z5]),(0,[z1018,z1,z2,z3,z4,z5])],[(0,[z70,z1,z2,z3,z4,z5]),(0,[z64,z1,z218,z3,z4,z5]),(0,[z12,z261,z2,z3,z4,z5]),(0,[z1,z2,z1019,z25,z4,z5]),(0,[z6,z1,z55,z178,z4,z5]),(0,[z6,z1020,z2,z3,z4,z5]),(0,[z1021,z261,z2,z3,z4,z5])],[(0,[z6,z1,z2,z3,z4,z1022]),(0,[z1,z2,z3,z145,z5,z15]),(0,[z1023,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z93,z333]),(0,[z1024,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z25,z4,z108]),(0,[z12,z1,z2,z3,z4,z1025]),(0,[z1,z2,z3,z4,z66,z1026]),(0,[z6,z2,z1027,z3,z4,z5]),(0,[z6,z1,z2,z4,z5,z1028]),(0,[z1,z2,z3,z4,z38,z279]),(0,[z1,z2,z3,z1029,z4,z5]),(0,[z6,z1,z62,z3,z4,z5])],[(0,[z12,z1,z2,z3,z498,z5]),(0,[z1,z2,z3,z1008,z13,z5]),(0,[z1,z2,z3,z25,z4,z413]),(0,[z26,z14,z77,z3,z4,z5]),(0,[z129,z26,z1,z221,z4,z5]),(0,[z80,z6,z1027,z3,z4,z5]),(0,[z191,z1,z2,z3,z4,z38]),(0,[z6,z164,z2,z3,z4,z38]),(1,[z6,z1,z3,z4,z781])],[(0,[z6,z1,z1030,z3,z4,z5]),(0,[z490,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z15,z38]),(0,[z2,z3,z4,z66,z38,z48]),(0,[z6,z1,z2,z3,z4,z1031]),(0,[z493,z1,z2,z3,z4,z66])],[(0,[z1,z2,z3,z4,z1032,z5]),(0,[z1,z2,z3,z4,z1033,z5]),(0,[z1,z2,z3,z4,z400,z15])],[(0,[z26,z1,z2,z3,z4,z48]),(0,[z6,z1,z2,z3,z4,z1034]),(0,[z909,z1,z2,z3,z4,z5]),(0,[z12,z1,z2,z65,z4,z17]),(0,[z1,z2,z3,z1035,z318,z5]),(0,[z436,z1,z2,z3,z4,z66]),(0,[z1,z2,z3,z4,z5,z1036])],[(0,[z1,z2,z3,z4,z309,z18]),(0,[z1,z2,z388,z25,z4,z5]),(1,[z2,z3,z4,z421,z38]),(0,[z110,z1,z2,z3,z120,z5]),(0,[z6,z1,z1037,z3,z4,z5])],[(0,[z1,z2,z3,z91,z4,z5]),(0,[z202,z1,z2,z3,z4,z38]),(0,[z1,z2,z3,z405,z4,z15]),(0,[z73,z1,z2,z44,z4,z38]),(0,[z1038,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z1039,z4,z5]),(0,[z6,z1,z2,z3,z4,z1040])],[(0,[z1,z2,z3,z4,z38,z1041]),(0,[z2,z3,z4,z235,z49,z38])],[(0,[z6,z1,z2,z3,z4,z1042]),(0,[z1043,z1,z2,z3,z4,z5]),(0,[z6,z1,z55,z3,z132,z5])],[(0,[z1,z2,z3,z25,z4,z63]),(0,[z8,z42,z2,z3,z49,z5]),(0,[z1044,z1,z2,z3,z4,z5]),(0,[z1045,z1,z2,z3,z4,z5]),(0,[z12,z14,z77,z3,z4,z5]),(0,[z6,z1046,z2,z3,z4,z5]),(0,[z6,z1,z2,z1047,z4,z5])],[(0,[z26,z1,z2,z3,z4,z149]),(0,[z1,z2,z3,z4,z1048,z5]),(0,[z6,z1,z2,z3,z1049,z5]),(0,[z1,z2,z3,z4,z5,z1050]),(0,[z147,z98,z1,z2,z3,z122])]],
   [[(0,[z1051,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z1052,z5]),(0,[z6,z1,z2,z339,z4,z66])],[(0,[z431,z1,z2,z3,z145,z5]),(0,[z81,z6,z1,z2,z4,z18]),(0,[z1,z2,z3,z1053,z4,z5])],[(0,[z45,z1,z2,z3,z4,z109]),(0,[z1054,z1,z2,z3,z4,z5]),(0,[z6,z1,z468,z310,z4,z5]),(0,[z256,z59,z2,z3,z4,z38]),(0,[z1055,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z1056])],[(0,[z26,z1,z2,z286,z4,z5]),(0,[z6,z1,z2,z3,z4,z1057]),(0,[z1058,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z1059,z4,z5]),(0,[z86,z87,z1,z3,z4,z40]),(0,[z6,z1,z1060,z3,z4,z5]),(0,[z1061,z1,z2,z3,z4,z5])],[(0,[z80,z45,z55,z3,z4,z5]),(0,[z6,z1,z1062,z3,z4,z5]),(0,[z39,z26,z1,z3,z114,z5]),(0,[z348,z1,z2,z3,z4,z66]),(0,[z6,z1,z2,z1063,z4,z5]),(0,[z6,z1,z2,z50,z69,z66]),(0,[z302,z1,z209,z3,z119,z5])],[(0,[z45,z1,z2,z3,z120,z5]),(0,[z1,z2,z3,z491,z4,z66])],[(0,[z1,z42,z2,z3,z4,z182]),(0,[z45,z1,z2,z3,z4,z82]),(0,[z12,z1,z1064,z3,z4,z5]),(0,[z12,z86,z1,z3,z4,z40]),(0,[z1,z2,z3,z1065,z4,z5]),(0,[z376,z1,z2,z3,z153,z5]),(0,[z6,z1,z1066,z3,z4,z5])],[(0,[z45,z1,z125,z3,z4,z5]),(0,[z1,z2,z3,z25,z4,z158]),(0,[z6,z1,z1067,z3,z4,z38]),(0,[z6,z1,z2,z3,z4,z447])],[(0,[z1068,z1,z2,z3,z4,z5]),(0,[z1069,z1,z2,z3,z4,z5])],[(0,[z1070,z1,z2,z3,z4,z5])],[(0,[z45,z92,z2,z3,z4,z66]),(0,[z6,z1,z2,z3,z4,z1071]),(0,[z1072,z1,z2,z3,z4,z5]),(0,[z1073,z1,z2,z3,z4,z5])],[(0,[z6,z1,z2,z1074,z4,z5]),(0,[z74,z1,z2,z3,z25,z66]),(0,[z1075,z1,z2,z3,z4,z5]),(0,[z1076,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z93,z96])],[(0,[z6,z1,z2,z3,z4,z1077]),(0,[z0,z1,z2,z3,z4,z391])],[(0,[z79,z1,z904,z3,z4,z5]),(0,[z202,z346,z2,z3,z4,z5]),(0,[z12,z1,z2,z3,z13,z5]),(0,[z1,z2,z3,z4,z5,z1078]),(0,[z1079,z1,z2,z3,z4,z5])],[(0,[z1,z425,z3,z25,z4,z5]),(0,[z1080,z1,z2,z3,z4,z5]),(0,[z6,z1,z125,z3,z4,z179]),(0,[z6,z1,z2,z3,z4,z1081]),(0,[z1,z1082,z2,z3,z4,z5])],[(0,[z1,z42,z2,z3,z4,z211]),(0,[z1083,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z179,z1084])]],
   [[(0,[z24,z42,z2,z3,z4,z38]),(0,[z1085,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1086])],[(0,[z1,z1087,z2,z3,z4,z5]),(0,[z80,z12,z55,z3,z4,z5]),(0,[z1,z2,z3,z4,z66,z1088]),(0,[z26,z1,z209,z3,z119,z5]),(0,[z39,z6,z1,z3,z173,z5]),(0,[z896,z1,z2,z3,z4,z66])],[(0,[z12,z1,z2,z3,z669,z5]),(0,[z6,z1,z2,z3,z4,z1089]),(0,[z12,z1,z2,z3,z4,z38]),(0,[z1,z2,z3,z1090,z4,z5]),(0,[z1091,z1,z2,z3,z4,z5]),(0,[z1092,z1,z2,z3,z4,z5]),(0,[z315,z1,z2,z3,z4,z38])],[(0,[z1093,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z1094,z4,z5]),(0,[z35,z1,z2,z46,z4,z5]),(0,[z199,z1,z2,z3,z4,z309]),(0,[z1,z2,z744,z25,z4,z5]),(0,[z6,z1,z2,z3,z318,z66])],[(0,[z45,z1,z2,z3,z4,z158]),(0,[z1,z2,z3,z4,z5,z1095]),(0,[z80,z234,z55,z3,z4,z5]),(0,[z527,z6,z55,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z1096]),(1,[z6,z2,z3,z817,z5]),(0,[z6,z1,z2,z3,z4,z1097])],[(0,[z6,z1,z2,z1098,z4,z5]),(0,[z1,z52,z53,z25,z4,z5]),(0,[z1,z2,z3,z4,z5,z1099]),(0,[z819,z1,z2,z3,z132,z5]),(0,[z6,z1,z1100,z3,z4,z5]),(0,[z451,z6,z2,z68,z4,z5]),(0,[z1101,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z1102,z4,z5]),(0,[z575,z1,z2,z3,z4,z66]),(0,[z6,z2,z3,z4,z66,z827])],[(0,[z19,z42,z2,z3,z4,z66]),(0,[z480,z1,z2,z3,z4,z15]),(0,[z139,z2,z3,z68,z4,z5]),(0,[z1,z2,z3,z4,z66,z1103])],[(0,[z6,z1,z2,z3,z4,z499]),(0,[z1,z2,z3,z4,z5,z1104]),(0,[z6,z1,z2,z1105,z4,z5]),(0,[z6,z1,z2,z1106,z4,z5])],[(0,[z86,z1,z3,z4,z15,z40]),(0,[z1107,z1,z2,z3,z4,z5]),(0,[z110,z1,z2,z3,z145,z5]),(0,[z1,z2,z3,z1108,z4,z38]),(0,[z1109,z1,z2,z3,z4,z5]),(0,[z1110,z1,z2,z3,z4,z5])],[(0,[z133,z1,z2,z310,z4,z5])],[(0,[z1111,z1,z2,z3,z4,z5]),(0,[z6,z1,z3,z792,z4,z5]),(0,[z6,z261,z2,z3,z4,z122])],[(0,[z1,z2,z3,z1112,z4,z5]),(0,[z1,z2,z3,z1113,z4,z5]),(0,[z26,z1,z2,z3,z4,z15]),(0,[z1,z2,z3,z4,z5,z1114]),(0,[z268,z1,z2,z3,z4,z167])],[(0,[z6,z1,z2,z3,z4,z1115]),(0,[z6,z1,z2,z921,z3,z5]),(0,[z278,z1,z62,z3,z4,z5])],[(0,[z171,z1,z2,z3,z4,z5]),(0,[z139,z2,z3,z11,z4,z5]),(0,[z1,z2,z3,z4,z94,z522]),(0,[z1,z2,z3,z4,z447,z15]),(0,[z177,z1,z2,z178,z4,z5]),(0,[z80,z6,z55,z3,z4,z461]),(0,[z219,z6,z1,z2,z4,z343]),(0,[z6,z1116,z2,z3,z4,z5]),(0,[z129,z417,z1,z221,z4,z5])],[(0,[z45,z1,z2,z3,z132,z5]),(0,[z12,z41,z1,z2,z4,z18]),(0,[z1,z2,z1117,z25,z4,z5]),(0,[z1,z2,z3,z4,z51,z811])],[(0,[z824,z1,z2,z3,z4,z5]),(0,[z1118,z1,z2,z3,z4,z5]),(0,[z1119,z1,z2,z3,z4,z5]),(0,[z1120,z1,z2,z3,z4,z5])]],
   [[(0,[z127,z1,z904,z3,z4,z5]),(0,[z129,z6,z1,z221,z4,z66]),(0,[z1,z2,z3,z4,z5,z1121]),(0,[z106,z6,z1,z2,z4,z18])],[(0,[z1,z42,z3,z845,z4,z5]),(0,[z1,z2,z3,z4,z5,z1122]),(0,[z6,z1,z2,z388,z4,z461]),(0,[z1,z2,z3,z1123,z4,z5]),(0,[z1,z2,z3,z4,z167,z1124]),(0,[z6,z1,z425,z310,z4,z5]),(0,[z6,z1125,z2,z3,z4,z5])],[(0,[z14,z77,z3,z25,z4,z5]),(0,[z1,z2,z3,z25,z4,z51])],[(0,[z112,z139,z2,z3,z4,z5]),(0,[z315,z1,z2,z3,z4,z15]),(0,[z26,z1,z2,z3,z4,z182]),(0,[z8,z6,z2,z3,z49,z182])],[(0,[z1126,z1,z2,z3,z4,z5]),(0,[z210,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z745,z4,z5]),(0,[z164,z2,z3,z25,z4,z5]),(0,[z6,z1,z2,z1127,z4,z5]),(0,[z1128,z1,z2,z3,z4,z391]),(0,[z1129,z1,z2,z3,z4,z5]),(0,[z6,z2,z3,z4,z817,z5]),(0,[z1,z34,z2,z3,z4,z214]),(0,[z1,z2,z3,z4,z5,z1130]),(0,[z147,z6,z1,z2,z286,z122])],[(0,[z1,z2,z3,z4,z66,z317]),(0,[z106,z1,z2,z3,z25,z4])],[(0,[z12,z411,z1,z2,z3,z4]),(0,[z6,z1,z2,z178,z4,z38]),(0,[z6,z1,z1131,z3,z4,z5])],[(0,[z1132,z1,z2,z3,z4,z5]),(0,[z45,z164,z2,z3,z4,z5]),(0,[z1,z2,z3,z25,z4,z66]),(0,[z1,z2,z3,z4,z15,z430]),(0,[z1,z2,z516,z4,z5,z100]),(0,[z1,z2,z286,z4,z5,z15]),(0,[z177,z1,z2,z3,z132,z5]),(0,[z226,z28,z2,z3,z11,z5]),(0,[z1133,z6,z1,z2,z3,z4]),(0,[z6,z1,z2,z1134,z4,z5]),(0,[z6,z1,z2,z3,z4,z1135])],[(0,[z288,z1,z2,z3,z176,z5]),(0,[z6,z1,z2,z3,z4,z461]),(0,[z348,z1,z2,z3,z4,z9]),(0,[z6,z261,z2,z286,z4,z5])],[(0,[z6,z1,z1136,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z1137]),(0,[z6,z1,z2,z3,z1138,z5]),(0,[z261,z932,z2,z3,z4,z5])],[(0,[z26,z1,z2,z3,z4,z445])],[(0,[z1,z32,z2,z3,z4,z5]),(0,[z833,z6,z1,z2,z4,z5]),(0,[z12,z1,z2,z3,z4,z182]),(0,[z1139,z1,z2,z3,z4,z5]),(0,[z1140,z1,z2,z3,z4,z5])],[(0,[z6,z1,z2,z3,z4,z1141]),(0,[z1,z2,z3,z4,z5,z1142]),(0,[z1,z2,z3,z170,z93,z5]),(0,[z6,z1,z503,z3,z119,z5]),(0,[z6,z1,z2,z3,z4,z1143])],[(0,[z6,z1,z2,z3,z4,z1144]),(0,[z8,z139,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1145]),(0,[z159,z2,z3,z4,z66,z15]),(0,[z1146,z6,z1,z2,z3,z4]),(0,[z1147,z1,z2,z3,z4,z5])],[(0,[z42,z2,z503,z3,z4,z5]),(0,[z45,z643,z2,z3,z4,z5]),(0,[z1148,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z1149,z4,z5]),(0,[z80,z6,z55,z3,z4,z5]),(0,[z39,z6,z1,z3,z114,z66]),(0,[z6,z1150,z2,z3,z4,z5]),(0,[z1151,z1,z2,z3,z4,z5])],[(0,[z6,z1,z2,z3,z4,z1152]),(0,[z1,z2,z3,z1153,z4,z38]),(0,[z1,z2,z3,z4,z437,z38]),(0,[z147,z26,z1,z2,z3,z122]),(0,[z1,z2,z3,z1154,z4,z5]),(0,[z1,z2,z3,z4,z7,z785]),(0,[z6,z672,z2,z3,z4,z66]),(0,[z1,z2,z3,z4,z5,z1155])]],
   [[(0,[z6,z1,z2,z3,z132,z38]),(0,[z925,z1,z2,z3,z4,z109]),(0,[z6,z1,z2,z310,z4,z5]),(0,[z6,z361,z2,z3,z4,z38])],[(0,[z250,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z1156])],[(0,[z6,z1,z2,z1157,z4,z5]),(0,[z256,z1,z2,z3,z4,z317]),(0,[z1,z2,z3,z1158,z4,z5]),(0,[z12,z1,z2,z3,z4,z802]),(0,[z1,z2,z178,z25,z4,z5]),(0,[z6,z1,z2,z3,z1159,z5]),(0,[z1160,z1,z2,z3,z4,z461]),(0,[z6,z1,z52,z274,z4,z5]),(0,[z1,z2,z3,z1161,z4,z5])],[(0,[z45,z42,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z1162,z5]),(0,[z1163,z1,z2,z3,z4,z5]),(0,[z56,z6,z1,z2,z574,z5]),(0,[z28,z34,z2,z3,z11,z5]),(0,[z1164,z1,z2,z3,z4,z5])],[(0,[z12,z1,z2,z3,z4,z211]),(0,[z376,z1,z2,z3,z13,z5]),(0,[z26,z1,z2,z65,z4,z17]),(0,[z1165,z1,z2,z3,z4,z5]),(0,[z1166,z1,z2,z3,z4,z5]),(0,[z6,z261,z2,z65,z3,z4])],[(0,[z1,z2,z3,z1167,z4,z5]),(0,[z6,z1,z2,z3,z145,z38]),(0,[z6,z1,z1168,z3,z4,z5]),(0,[z6,z1,z2,z3,z93,z357])],[(0,[z1169,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z318,z158])],[(0,[z92,z784,z2,z3,z4,z5]),(0,[z12,z1,z2,z3,z25,z38]),(0,[z1,z2,z3,z1035,z4,z5]),(0,[z1,z2,z3,z1170,z4,z5]),(0,[z527,z6,z2,z3,z49,z5]),(0,[z6,z1,z2,z3,z418,z96])],[(0,[z543,z1,z2,z3,z25,z5]),(0,[z1,z2,z3,z25,z4,z109]),(0,[z6,z1,z2,z3,z4,z1171]),(0,[z6,z1,z2,z3,z4,z1172])],[(0,[z6,z1,z2,z3,z4,z5]),(1,[z784,z2,z3,z4,z5]),(0,[z12,z1,z816,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1173]),(0,[z376,z1,z2,z3,z4,z38]),(0,[z6,z1,z2,z3,z4,z1174]),(0,[z1,z2,z3,z289,z4,z38]),(0,[z86,z6,z1,z3,z4,z246]),(0,[z1175,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z921,z4,z5]),(0,[z1,z1176,z2,z3,z4,z5])],[(0,[z26,z1,z2,z3,z4,z337]),(0,[z130,z1,z2,z3,z4,z38]),(0,[z1,z2,z3,z941,z4,z82])],[(0,[z1,z2,z3,z25,z120,z5]),(0,[z1,z2,z3,z1177,z4,z5])],[(0,[z1,z2,z3,z25,z4,z82]),(0,[z141,z110,z2,z68,z4,z5]),(0,[z6,z1,z2,z275,z4,z38]),(0,[z1178,z1,z2,z3,z4,z5])],[(0,[z12,z139,z2,z3,z4,z38]),(0,[z1,z2,z3,z4,z116,z309]),(0,[z1,z2,z3,z4,z1179,z5]),(0,[z1,z2,z3,z742,z145,z5]),(0,[z1180,z1,z2,z3,z4,z5])],[(0,[z6,z1,z2,z3,z4,z1181]),(1,[z1,z2,z3,z4,z846]),(0,[z26,z159,z2,z3,z4,z66]),(0,[z1,z2,z3,z4,z5,z1182]),(0,[z6,z1,z2,z3,z4,z7]),(0,[z6,z1,z1183,z3,z4,z5]),(0,[z6,z1,z2,z734,z4,z5]),(0,[z1,z1184,z2,z3,z4,z5])],[(0,[z1185,z1,z2,z3,z4,z5]),(0,[z501,z1,z2,z253,z4,z5]),(0,[z1186,z1,z2,z3,z4,z5])]],
   [[(0,[z1,z2,z166,z3,z25,z5]),(0,[z1,z2,z3,z1187,z4,z5]),(0,[z1188,z1,z2,z3,z4,z5]),(0,[z302,z1,z2,z3,z4,z38]),(0,[z411,z927,z1,z2,z3,z4])],[(0,[z699,z1,z2,z3,z25,z5]),(0,[z12,z1,z2,z3,z4,z835]),(0,[z1,z2,z3,z4,z5,z1124]),(0,[z86,z26,z1,z3,z4,z40]),(0,[z1,z2,z3,z4,z94,z846]),(1,[z6,z1,z792,z4,z5]),(0,[z6,z1,z99,z3,z4,z116])],[(0,[z138,z1,z2,z46,z4,z5]),(0,[z1,z2,z3,z4,z9,z15]),(0,[z268,z14,z77,z3,z4,z5]),(0,[z6,z14,z77,z3,z4,z167]),(0,[z6,z1,z425,z3,z4,z66]),(0,[z1189,z1,z2,z3,z4,z5]),(0,[z41,z233,z1,z2,z4,z18])],[(0,[z256,z1,z2,z3,z4,z5]),(0,[z2,z3,z4,z5,z437,z48]),(0,[z1160,z1,z2,z3,z4,z5]),(0,[z141,z6,z2,z68,z4,z5]),(0,[z6,z28,z2,z3,z4,z182]),(0,[z1,z2,z3,z4,z38,z1190]),(0,[z6,z1,z52,z53,z4,z66]),(0,[z1,z1191,z2,z3,z4,z5]),(0,[z1192,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z153,z93,z96])],[(0,[z0,z1,z2,z3,z4,z5]),(0,[z1,z1193,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z1194]),(0,[z141,z2,z68,z4,z5,z15]),(0,[z1,z2,z3,z4,z492,z15]),(0,[z6,z2,z3,z4,z437,z38])],[(0,[z6,z1,z327,z3,z4,z5]),(0,[z6,z1,z2,z1195,z4,z5]),(0,[z1,z2,z3,z4,z5,z1196])],[(0,[z79,z1,z306,z3,z4,z5]),(0,[z12,z159,z2,z3,z4,z66]),(0,[z1197,z1,z2,z3,z4,z5]),(0,[z315,z159,z2,z3,z4,z66])],[(0,[z12,z1,z2,z3,z359,z5]),(0,[z1,z2,z3,z1198,z4,z5]),(0,[z6,z1,z2,z3,z4,z1199]),(0,[z1,z1200,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z1008,z5]),(0,[z106,z1,z2,z3,z4,z15]),(1,[z6,z1027,z3,z4,z5]),(0,[z1004,z1,z2,z3,z4,z66]),(0,[z129,z1,z491,z221,z4,z5])],[(0,[z1,z34,z2,z3,z4,z5]),(0,[z1,z2,z495,z3,z4,z15]),(0,[z1201,z1,z2,z3,z4,z5]),(0,[z6,z2,z3,z4,z964,z38]),(0,[z1202,z1,z2,z3,z4,z38]),(0,[z6,z1,z2,z3,z4,z1203]),(0,[z129,z6,z1,z792,z4,z5])],[(0,[z6,z1,z2,z3,z4,z1204]),(0,[z12,z24,z2,z3,z4,z38]),(0,[z1205,z1,z2,z3,z4,z5]),(0,[z1206,z1,z2,z3,z4,z5])],[(0,[z127,z1,z88,z3,z4,z5]),(0,[z6,z1,z2,z1019,z4,z5]),(0,[z446,z1,z2,z31,z4,z5]),(0,[z6,z1,z2,z388,z4,z66]),(0,[z6,z14,z1027,z3,z4,z5]),(0,[z6,z420,z77,z3,z4,z5]),(0,[z6,z1207,z2,z3,z4,z5])],[(0,[z45,z354,z2,z3,z4,z5]),(0,[z1,z88,z904,z3,z4,z5]),(0,[z1,z2,z3,z25,z4,z9]),(0,[z226,z1,z2,z3,z4,z66]),(0,[z1,z2,z3,z4,z66,z279])],[(0,[z1,z2,z3,z4,z5,z48]),(0,[z45,z784,z2,z3,z4,z5]),(0,[z1,z1208,z3,z25,z4,z5]),(0,[z1209,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z1210,z5]),(0,[z6,z28,z2,z3,z11,z214]),(0,[z315,z1,z2,z3,z4,z217])],[(0,[z1211,z1,z2,z3,z4,z5]),(0,[z26,z1,z2,z3,z4,z38]),(0,[z8,z6,z2,z3,z49,z38]),(0,[z1212,z1,z2,z3,z4,z5]),(0,[z411,z302,z1,z2,z3,z4]),(0,[z147,z76,z1,z2,z3,z122])],[(0,[z232,z1,z2,z3,z4,z5]),(0,[z199,z1,z2,z3,z4,z846]),(0,[z70,z1,z2,z3,z4,z66]),(0,[z1213,z1,z2,z3,z4,z5])],[(0,[z1,z139,z2,z3,z4,z5]),(0,[z141,z6,z327,z68,z4,z5]),(0,[z6,z1,z2,z3,z120,z179]),(0,[z1214,z1,z2,z3,z4,z5])]],
   [[(0,[z1,z2,z3,z4,z15,z391]),(0,[z1215,z1,z2,z3,z4,z5]),(0,[z6,z1,z62,z3,z4,z66]),(0,[z1216,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z1217,z4,z5])],[(0,[z1218,z1,z2,z3,z4,z5]),(0,[z1219,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1220])],[(0,[z202,z1,z2,z3,z440,z5]),(0,[z1221,z1,z2,z3,z4,z5]),(0,[z12,z1,z2,z339,z4,z5]),(0,[z1,z1222,z2,z3,z4,z5]),(0,[z1,z1223,z2,z3,z4,z5]),(0,[z490,z1,z2,z3,z4,z66])],[(0,[z1,z2,z1224,z3,z4,z5])],[(0,[z1225,z1,z2,z3,z4,z5]),(0,[z41,z45,z1,z2,z4,z18]),(0,[z1,z2,z3,z25,z132,z5]),(0,[z2,z3,z4,z5,z437,z38]),(0,[z6,z1,z2,z1226,z4,z5]),(0,[z1,z32,z2,z3,z4,z109]),(0,[z1227,z1,z2,z3,z4,z5]),(0,[z6,z2,z503,z3,z4,z38]),(0,[z325,z1,z2,z3,z4,z38]),(0,[z76,z1,z62,z3,z4,z5])],[(0,[z1,z2,z3,z4,z1228,z5]),(0,[z6,z1,z99,z3,z4,z319]),(0,[z1,z2,z3,z1229,z4,z5])],[(0,[z543,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1230]),(0,[z1,z2,z3,z91,z4,z66]),(0,[z6,z1,z2,z3,z4,z1231]),(0,[z26,z1,z2,z889,z4,z5]),(0,[z268,z1,z2,z3,z4,z38]),(0,[z159,z2,z3,z4,z66,z217]),(0,[z411,z6,z1,z146,z3,z4]),(0,[z1,z2,z3,z4,z5,z1232])],[(0,[z89,z1,z2,z3,z91,z5]),(0,[z45,z1,z2,z178,z4,z5]),(0,[z45,z169,z2,z3,z4,z5]),(0,[z1233,z6,z1,z2,z3,z4])],[(0,[z45,z1,z2,z3,z4,z9]),(0,[z1234,z1,z2,z3,z4,z5]),(0,[z6,z1,z1235,z3,z4,z5]),(0,[z1,z99,z3,z25,z4,z116]),(0,[z1,z2,z3,z25,z5,z142]),(0,[z1236,z1,z2,z3,z4,z5]),(0,[z6,z352,z77,z3,z4,z5]),(0,[z6,z1,z327,z3,z4,z51]),(0,[z1,z1237,z2,z3,z4,z5])],[(0,[z1,z2,z3,z25,z145,z5])],[(0,[z1238,z1,z2,z3,z4,z5]),(0,[z1,z1239,z2,z3,z4,z5]),(0,[z1,z1240,z2,z3,z4,z5])],[(0,[z314,z1,z306,z3,z4,z5]),(0,[z1241,z1,z2,z3,z4,z5])],[(0,[z6,z1,z2,z1242,z4,z5]),(0,[z141,z45,z2,z68,z4,z5]),(0,[z26,z1,z2,z3,z4,z94]),(0,[z6,z1,z2,z50,z447,z69]),(0,[z1243,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1244]),(0,[z98,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z846,z15]),(0,[z1,z2,z3,z4,z5,z1245]),(0,[z6,z2,z441,z3,z4,z38]),(0,[z1,z2,z3,z1246,z4,z447])],[(0,[z6,z477,z2,z3,z4,z38]),(0,[z6,z1,z2,z3,z4,z1247]),(1,[z6,z1,z3,z750,z5])],[(0,[z1,z1248,z2,z3,z4,z5]),(0,[z1,z327,z3,z25,z4,z5]),(0,[z8,z133,z2,z3,z49,z5]),(0,[z6,z1,z2,z1063,z4,z66]),(0,[z147,z6,z1,z2,z3,z67])]],
   [[(0,[z278,z1,z2,z3,z4,z5]),(0,[z147,z6,z1,z2,z3,z290])],[(1,[z1,z904,z3,z4,z5]),(0,[z1,z2,z3,z1065,z4,z66])],[(0,[z6,z1,z2,z3,z4,z108]),(0,[z1,z2,z3,z4,z5,z1249]),(0,[z87,z1,z2,z3,z4,z38]),(0,[z6,z2,z3,z4,z66,z488]),(0,[z1,z2,z3,z4,z66,z370]),(0,[z1,z2,z3,z1250,z4,z5])],[(0,[z6,z1,z2,z3,z4,z413]),(0,[z6,z164,z2,z3,z4,z214]),(0,[z6,z1,z2,z3,z4,z1251])],[(0,[z315,z1,z2,z3,z4,z94]),(0,[z1252,z1,z2,z3,z4,z5]),(0,[z6,z1,z327,z68,z4,z5])],[(0,[z1,z2,z3,z120,z5,z15]),(0,[z6,z2,z3,z4,z38,z581]),(0,[z6,z1,z3,z4,z66,z1253])],[(0,[z28,z42,z2,z3,z4,z38]),(0,[z45,z1,z2,z3,z145,z5]),(0,[z6,z1,z468,z3,z4,z66])],[(0,[z12,z2,z3,z4,z66,z38]),(0,[z234,z1,z2,z3,z318,z5]),(0,[z6,z1,z125,z3,z4,z5]),(0,[z6,z1,z2,z339,z4,z9]),(0,[z315,z2,z3,z4,z66,z38])],[(0,[z1,z42,z2,z3,z4,z179]),(0,[z6,z1254,z2,z3,z4,z5]),(0,[z131,z1,z2,z3,z4,z5]),(0,[z12,z1,z2,z906,z4,z5]),(0,[z12,z1,z2,z3,z13,z66]),(0,[z59,z2,z3,z4,z5,z38]),(0,[z6,z1,z2,z3,z1255,z5]),(0,[z1256,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1257]),(0,[z147,z6,z1,z62,z3,z122])],[(0,[z6,z1,z2,z3,z4,z1258]),(0,[z12,z1,z2,z3,z407,z5]),(0,[z141,z12,z2,z68,z4,z5]),(0,[z80,z6,z55,z3,z4,z158]),(0,[z1259,z1,z2,z3,z4,z5]),(0,[z1260,z1,z2,z3,z4,z5])],[(0,[z6,z547,z2,z3,z4,z66]),(0,[z1,z1261,z2,z3,z4,z5]),(0,[z1262,z1,z2,z3,z4,z5]),(0,[z1263,z1,z2,z3,z4,z5])],[(0,[z6,z1,z2,z3,z4,z63]),(0,[z95,z1,z118,z3,z4,z5]),(0,[z12,z1,z2,z3,z4,z391]),(0,[z1,z2,z3,z4,z461,z1249]),(0,[z1085,z1,z2,z3,z4,z66])],[(0,[z1264,z1,z2,z3,z4,z5]),(0,[z139,z2,z55,z3,z4,z5]),(0,[z1265,z1,z2,z3,z4,z179]),(0,[z8,z428,z2,z3,z49,z5]),(0,[z6,z322,z2,z3,z4,z38]),(0,[z1266,z1,z2,z3,z4,z5]),(0,[z147,z1,z2,z3,z279,z122])],[(0,[z45,z1,z2,z275,z4,z5]),(0,[z6,z1,z2,z388,z4,z158]),(0,[z1267,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z145,z179]),(0,[z1268,z1,z2,z3,z4,z5]),(0,[z6,z28,z2,z3,z4,z38]),(0,[z240,z6,z2,z3,z49,z38])],[(0,[z1,z2,z3,z4,z5,z15]),(0,[z35,z1,z2,z46,z4,z66]),(0,[z1269,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z1270]),(0,[z6,z1,z146,z3,z4,z5])],[(0,[z26,z1,z2,z3,z4,z211]),(0,[z1,z2,z1271,z3,z4,z5]),(0,[z1,z2,z3,z4,z66,z345]),(0,[z210,z1,z99,z3,z4,z116])]],
   [[(0,[z1,z42,z2,z339,z4,z5]),(0,[z1272,z1,z42,z2,z4,z5]),(0,[z1,z42,z52,z53,z4,z5]),(0,[z6,z1,z2,z3,z4,z1273]),(0,[z127,z1,z595,z3,z4,z5]),(0,[z12,z56,z1,z2,z10,z5]),(0,[z28,z2,z3,z4,z15,z38]),(0,[z6,z28,z2,z3,z11,z5]),(0,[z6,z1,z1274,z2,z3,z4]),(0,[z1275,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z499,z48]),(0,[z1,z2,z3,z153,z4,z5]),(0,[z288,z1,z2,z3,z4,z38]),(0,[z28,z2,z3,z187,z11,z5])],[(0,[z154,z1,z2,z3,z4,z48]),(0,[z79,z1,z71,z3,z4,z5]),(0,[z6,z1,z1276,z3,z4,z5]),(0,[z12,z1,z2,z3,z170,z5]),(0,[z605,z2,z3,z4,z15,z38]),(0,[z6,z261,z2,z3,z4,z38]),(0,[z1,z34,z2,z3,z4,z413])],[(0,[z12,z933,z2,z3,z4,z5]),(0,[z6,z1277,z2,z3,z4,z5]),(0,[z6,z1,z977,z3,z4,z5]),(0,[z6,z1,z859,z3,z4,z5])],[(0,[z1,z59,z2,z3,z4,z5]),(0,[z1,z42,z2,z50,z69,z5]),(0,[z79,z1,z118,z3,z4,z38]),(0,[z1,z2,z3,z4,z38,z795]),(0,[z6,z1,z2,z3,z4,z158]),(0,[z6,z1,z1278,z3,z4,z5]),(0,[z1,z366,z2,z3,z4,z38]),(0,[z6,z1,z2,z3,z4,z1279])],[(0,[z6,z1,z2,z3,z4,z1280])],[(0,[z411,z1,z42,z2,z3,z4]),(0,[z26,z1,z2,z3,z4,z1088]),(0,[z1281,z6,z1,z2,z3,z4])],[(0,[z6,z1,z2,z3,z4,z1282]),(0,[z1283,z1,z2,z3,z4,z5]),(0,[z12,z106,z1,z2,z3,z4]),(0,[z2,z3,z25,z4,z66,z38]),(0,[z1,z2,z3,z4,z38,z522]),(0,[z1,z2,z3,z4,z461,z15]),(0,[z1,z162,z3,z4,z5,z475]),(0,[z999,z1,z2,z3,z145,z5]),(0,[z1284,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z182,z1099]),(0,[z256,z28,z2,z3,z4,z38])],[(0,[z56,z45,z1,z2,z10,z5]),(0,[z45,z1,z2,z286,z4,z5]),(0,[z171,z1,z2,z3,z4,z66]),(0,[z1,z2,z3,z4,z5,z1285])],[(0,[z1286,z1,z2,z3,z4,z5]),(0,[z1287,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z814]),(0,[z6,z1,z2,z178,z318,z5]),(0,[z1288,z1,z2,z3,z4,z38]),(0,[z1289,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z1290,z4,z5])],[(0,[z1291,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1292])],[(0,[z6,z1,z2,z1293,z4,z5]),(0,[z1,z2,z3,z93,z96,z370])],[(0,[z1,z2,z3,z1294,z4,z5]),(0,[z1,z42,z62,z3,z4,z5]),(0,[z73,z1,z2,z512,z4,z5]),(0,[z6,z14,z77,z3,z4,z38]),(0,[z133,z1,z2,z3,z4,z66])],[(0,[z950,z1,z2,z3,z4,z5]),(0,[z1295,z1,z2,z3,z4,z5]),(0,[z41,z6,z1,z2,z4,z18])],[(0,[z6,z1,z2,z1296,z4,z5]),(0,[z1,z2,z3,z4,z1297,z5]),(0,[z6,z112,z2,z111,z4,z38]),(0,[z210,z1,z2,z3,z4,z66]),(0,[z1298,z1,z2,z3,z4,z5])]],
   [[(0,[z1,z2,z3,z4,z66,z437]),(0,[z6,z1,z1299,z3,z4,z5]),(0,[z1,z2,z3,z4,z217,z38]),(0,[z1300,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z1301,z5]),(0,[z1,z2,z3,z4,z15,z529]),(0,[z1,z2,z3,z1090,z120,z5]),(0,[z1302,z1,z2,z3,z4,z5])],[(0,[z86,z6,z261,z2,z3,z4])],[(0,[z1,z42,z2,z3,z318,z5]),(0,[z1,z2,z3,z4,z5,z1303]),(0,[z41,z6,z1,z2,z4,z343]),(0,[z1304,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1305])],[(0,[z1,z2,z3,z157,z4,z447])],[(0,[z26,z1,z2,z3,z4,z148]),(0,[z8,z2,z3,z49,z5,z15])],[(0,[z1,z2,z3,z187,z4,z5]),(0,[z45,z1,z209,z3,z119,z5]),(0,[z508,z6,z1,z221,z4,z5]),(0,[z1,z32,z2,z3,z4,z66]),(0,[z147,z278,z1,z2,z3,z122]),(0,[z6,z164,z62,z3,z4,z5])],[(0,[z45,z1,z2,z3,z4,z167]),(0,[z1,z2,z3,z1306,z4,z5]),(0,[z191,z1,z2,z3,z4,z5]),(0,[z26,z1,z2,z3,z4,z217])],[(0,[z1307,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z1308]),(0,[z1309,z1,z2,z3,z4,z38])],[(0,[z1,z42,z2,z3,z4,z391]),(0,[z42,z2,z3,z530,z4,z5]),(0,[z1,z1310,z2,z3,z4,z5]),(0,[z45,z507,z2,z3,z4,z5]),(0,[z1,z2,z1296,z25,z4,z5]),(0,[z1,z1311,z2,z3,z4,z5]),(0,[z80,z6,z55,z3,z4,z66]),(0,[z1312,z1,z2,z3,z4,z38]),(0,[z56,z6,z1,z2,z537,z5])],[(0,[z42,z2,z3,z4,z421,z5]),(0,[z12,z1,z2,z3,z450,z5]),(0,[z6,z1,z468,z3,z4,z9]),(0,[z269,z6,z1,z3,z4,z311]),(0,[z6,z1,z2,z286,z4,z38])],[(0,[z1313,z1,z2,z3,z4,z5]),(0,[z12,z2,z3,z4,z49,z38]),(0,[z6,z2,z3,z948,z4,z5]),(0,[z6,z1,z2,z310,z4,z66]),(0,[z6,z444,z2,z3,z4,z38]),(0,[z1,z1314,z2,z3,z4,z5])],[(0,[z73,z1,z2,z44,z4,z5]),(1,[z1,z2,z3,z1008,z5]),(0,[z1,z172,z3,z4,z569,z5]),(0,[z0,z1,z2,z3,z4,z7]),(0,[z250,z1,z2,z3,z4,z66])],[(0,[z12,z1,z2,z3,z4,z179]),(0,[z256,z1,z2,z3,z4,z437]),(0,[z26,z1,z2,z339,z4,z5]),(0,[z8,z6,z2,z339,z49,z5]),(0,[z1,z2,z3,z4,z235,z38]),(0,[z315,z1,z2,z3,z4,z148])],[(0,[z45,z42,z2,z3,z4,z66]),(0,[z128,z1,z118,z3,z4,z5]),(0,[z288,z1,z2,z3,z170,z5]),(0,[z261,z2,z3,z4,z5,z15]),(0,[z1,z2,z3,z4,z1315,z5]),(0,[z714,z1,z2,z3,z4,z38])],[(0,[z1,z42,z2,z3,z4,z447]),(0,[z1,z2,z3,z1246,z4,z5]),(0,[z6,z1,z2,z3,z4,z51]),(0,[z1,z2,z3,z4,z5,z1316])]],
   [[(0,[z6,z1317,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1318]),(0,[z6,z1,z1168,z3,z4,z66])],[(0,[z376,z1,z2,z3,z5,z78]),(0,[z26,z1,z2,z50,z69,z5])],[(0,[z6,z1,z2,z3,z1319,z5]),(0,[z1320,z1,z2,z3,z4,z5]),(0,[z1,z1321,z2,z3,z4,z5]),(0,[z1,z99,z3,z4,z116,z345])],[(0,[z1,z42,z468,z3,z4,z5]),(0,[z1,z42,z2,z3,z93,z96]),(0,[z8,z6,z2,z3,z817,z5]),(0,[z1322,z1,z2,z3,z4,z5])],[(0,[z6,z1,z2,z3,z4,z66]),(0,[z1,z395,z2,z3,z4,z48]),(0,[z154,z1,z2,z3,z4,z15]),(0,[z234,z1,z2,z3,z4,z461]),(0,[z1323,z1,z2,z3,z4,z5]),(0,[z1,z1324,z2,z3,z4,z5]),(0,[z126,z1,z2,z3,z93,z96])],[(0,[z12,z1,z52,z53,z4,z5]),(0,[z6,z1,z2,z3,z1325,z5]),(0,[z6,z1,z2,z3,z4,z1326]),(0,[z39,z6,z1,z3,z115,z5]),(0,[z278,z1,z146,z3,z4,z5])],[(0,[z42,z2,z3,z4,z5,z437])],[(0,[z1,z2,z3,z4,z5,z217]),(0,[z26,z1,z2,z3,z4,z347]),(0,[z1,z2,z3,z1327,z4,z5]),(0,[z147,z1,z2,z3,z4,z522]),(0,[z6,z1,z2,z3,z1328,z5]),(0,[z1,z1329,z2,z3,z4,z5]),(0,[z1330,z1,z2,z3,z4,z5])],[(0,[z45,z1,z2,z3,z4,z182]),(0,[z76,z1,z2,z3,z4,z5]),(0,[z6,z1,z1067,z3,z4,z5]),(0,[z417,z1,z2,z3,z4,z38]),(0,[z6,z1,z209,z3,z119,z38]),(0,[z325,z1,z2,z50,z69,z5])],[(0,[z6,z1,z2,z3,z1331,z5]),(0,[z12,z1,z2,z50,z69,z5]),(0,[z141,z6,z2,z68,z4,z51]),(0,[z1218,z1,z2,z3,z4,z7]),(0,[z6,z1,z2,z1332,z4,z5]),(0,[z1333,z1,z2,z3,z4,z5])],[(0,[z543,z1,z2,z3,z187,z5]),(0,[z6,z28,z2,z3,z11,z413]),(0,[z1334,z1,z2,z3,z4,z5])],[(0,[z467,z1,z577,z3,z4,z5]),(0,[z1,z904,z118,z3,z4,z5]),(0,[z1,z2,z3,z25,z257,z5]),(0,[z1,z2,z3,z4,z421,z38]),(0,[z2,z3,z25,z4,z49,z38])],[(0,[z105,z1,z2,z3,z4,z309]),(0,[z1,z2,z388,z4,z5,z15]),(0,[z6,z1,z2,z1335,z4,z5]),(0,[z6,z28,z2,z3,z584,z5]),(0,[z6,z1,z2,z4,z38,z878])],[(0,[z1,z42,z2,z3,z4,z214]),(0,[z26,z1,z2,z3,z4,z465]),(0,[z26,z59,z2,z3,z4,z38]),(0,[z576,z6,z1,z221,z4,z5]),(0,[z1,z427,z2,z3,z4,z38]),(0,[z1,z2,z3,z1336,z4,z5])],[(0,[z1,z2,z3,z1337,z4,z5]),(0,[z256,z1,z2,z3,z4,z66]),(0,[z1,z2,z3,z4,z17,z309]),(0,[z159,z2,z3,z25,z4,z66]),(0,[z1,z2,z3,z25,z5,z151]),(0,[z234,z1,z2,z388,z4,z5]),(0,[z1,z1338,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z1339,z5]),(0,[z428,z1,z2,z3,z4,z38]),(0,[z761,z1,z2,z3,z4,z38]),(0,[z1340,z1,z2,z3,z4,z5])],[(0,[z1,z42,z2,z3,z4,z499]),(0,[z26,z1,z2,z3,z4,z379]),(0,[z1341,z1,z2,z3,z4,z5]),(0,[z1128,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z66]),(0,[z1,z2,z65,z4,z17,z517])]],
   [[(0,[z74,z1,z2,z3,z91,z5]),(0,[z6,z1,z2,z3,z4,z1342]),(0,[z6,z1,z2,z3,z4,z1343]),(0,[z1,z2,z3,z25,z188,z5]),(0,[z26,z1,z2,z3,z318,z5]),(0,[z431,z1,z2,z3,z4,z38]),(0,[z6,z1,z327,z3,z4,z66])],[(0,[z208,z1,z3,z609,z4,z5]),(0,[z133,z1,z2,z3,z4,z9]),(0,[z6,z1,z1344,z3,z4,z5]),(0,[z1,z2,z3,z1345,z4,z5])],[(0,[z12,z1,z62,z3,z4,z5]),(0,[z1,z2,z310,z25,z4,z5]),(0,[z41,z1,z2,z4,z15,z18]),(0,[z80,z26,z55,z3,z4,z5]),(0,[z26,z2,z3,z4,z66,z38]),(0,[z6,z1,z3,z4,z38,z888]),(0,[z1,z2,z3,z1346,z4,z5]),(0,[z56,z6,z1,z2,z10,z5]),(0,[z6,z1347,z2,z3,z4,z5])],[(0,[z45,z261,z2,z3,z4,z5]),(0,[z1,z34,z2,z3,z4,z66]),(0,[z1,z2,z50,z157,z69,z5])],[(0,[z73,z1,z2,z31,z4,z5]),(0,[z1,z1348,z3,z25,z4,z5]),(0,[z147,z1,z2,z3,z15,z122]),(0,[z6,z1349,z2,z3,z4,z5]),(0,[z6,z1,z209,z3,z750,z5]),(0,[z6,z1,z2,z3,z4,z1350]),(0,[z106,z6,z1,z2,z3,z4])],[(0,[z234,z1,z2,z3,z4,z5]),(0,[z1,z395,z2,z3,z4,z38]),(0,[z127,z1,z88,z3,z4,z66]),(0,[z1,z2,z3,z4,z5,z1351]),(0,[z6,z1,z2,z3,z4,z109]),(0,[z1,z2,z3,z4,z5,z1352]),(0,[z6,z1,z2,z3,z1353,z5])],[(0,[z35,z1,z2,z180,z4,z5]),(0,[z12,z1,z2,z3,z4,z1034]),(0,[z1354,z1,z2,z3,z4,z5]),(0,[z26,z1,z2,z3,z4,z391]),(0,[z6,z1,z2,z3,z4,z1355]),(0,[z1356,z1,z2,z3,z4,z447]),(0,[z1357,z1,z2,z3,z4,z5])],[(0,[z233,z1,z2,z3,z4,z38]),(0,[z6,z1,z195,z3,z4,z116]),(0,[z129,z171,z1,z221,z4,z5]),(0,[z1358,z1,z2,z3,z4,z5]),(0,[z1359,z1,z2,z3,z4,z5])],[(0,[z6,z1,z2,z3,z4,z1360]),(0,[z12,z1,z2,z3,z318,z5]),(0,[z1361,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z120,z5]),(0,[z6,z1,z2,z3,z4,z1362])],[(0,[z1,z308,z349,z3,z4,z5]),(0,[z1,z2,z3,z1108,z4,z5]),(0,[z45,z1,z2,z65,z4,z17]),(0,[z1,z2,z3,z4,z15,z499]),(0,[z6,z1,z425,z3,z4,z9]),(0,[z6,z1,z2,z3,z4,z1363]),(0,[z232,z1,z2,z3,z4,z66]),(0,[z6,z1,z2,z3,z4,z82])],[(0,[z6,z1,z2,z1364,z4,z5]),(0,[z1,z139,z2,z3,z4,z66]),(0,[z866,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z1365,z4,z5])],[(0,[z12,z1046,z2,z3,z4,z5]),(0,[z56,z1,z2,z10,z25,z5]),(0,[z348,z1,z2,z3,z4,z182]),(0,[z229,z1,z2,z3,z4,z38])],[(0,[z28,z42,z2,z3,z11,z5]),(0,[z12,z1,z2,z3,z440,z5]),(0,[z6,z1,z2,z3,z4,z1366]),(0,[z80,z6,z55,z178,z4,z5]),(0,[z6,z1,z2,z3,z4,z1367]),(0,[z1,z1368,z2,z3,z4,z5]),(0,[z24,z575,z2,z3,z4,z38]),(0,[z6,z2,z3,z4,z827,z38])],[(0,[z1,z1369,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1026]),(0,[z39,z1,z3,z114,z25,z5]),(0,[z1370,z1,z2,z3,z4,z5])],[(0,[z199,z1,z2,z3,z4,z48]),(0,[z45,z14,z77,z3,z4,z5]),(0,[z1371,z1,z2,z3,z4,z5]),(0,[z1,z209,z3,z289,z119,z5])],[(0,[z1372,z1,z2,z3,z4,z5]),(0,[z41,z26,z1,z2,z4,z18]),(0,[z6,z2,z3,z11,z817,z5]),(0,[z1,z1373,z2,z3,z4,z5])]],
   [[(0,[z1,z42,z2,z3,z4,z461]),(0,[z45,z112,z2,z111,z4,z5]),(0,[z26,z1,z2,z3,z4,z660]),(0,[z1374,z1,z2,z3,z4,z5]),(0,[z6,z2,z3,z4,z421,z38]),(0,[z1,z425,z3,z4,z5,z15]),(0,[z2,z3,z4,z66,z15,z38]),(0,[z26,z1,z468,z3,z4,z5]),(0,[z26,z1,z2,z3,z93,z96]),(0,[z8,z6,z468,z3,z49,z5]),(0,[z1,z2,z3,z4,z5,z863]),(0,[z1375,z1,z2,z3,z4,z5])],[(0,[z543,z1,z2,z3,z4,z66]),(0,[z6,z1,z2,z3,z4,z1376]),(0,[z139,z2,z3,z4,z5,z38]),(0,[z12,z1,z1062,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z846]),(0,[z1377,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z1378,z5])],[(0,[z1,z42,z425,z3,z4,z5]),(0,[z1379,z1,z2,z3,z4,z5]),(0,[z1380,z1,z2,z3,z4,z5])],[(0,[z6,z1,z2,z3,z4,z1381]),(0,[z1236,z1,z2,z3,z4,z66]),(0,[z1382,z1,z2,z3,z4,z5])],[(0,[z1,z395,z2,z3,z4,z94]),(0,[z12,z1,z2,z3,z4,z447]),(0,[z6,z1,z327,z3,z120,z5]),(0,[z141,z6,z125,z68,z4,z5]),(0,[z6,z1,z209,z3,z82,z119])],[(0,[z42,z2,z3,z645,z4,z5]),(0,[z871,z1,z2,z3,z4,z5])],[(0,[z1,z395,z2,z3,z4,z15]),(0,[z1,z2,z3,z157,z4,z5]),(0,[z80,z6,z55,z3,z132,z5]),(0,[z1383,z1,z2,z3,z4,z5]),(0,[z6,z1,z327,z111,z4,z5]),(0,[z568,z6,z2,z3,z4,z38]),(0,[z6,z1384,z2,z3,z4,z5]),(0,[z147,z6,z1,z146,z3,z122]),(0,[z1385,z1,z2,z3,z4,z5])],[(0,[z202,z139,z2,z3,z4,z5]),(0,[z12,z1,z2,z3,z4,z1071]),(0,[z1,z52,z53,z4,z5,z15]),(0,[z141,z26,z2,z68,z4,z5]),(0,[z6,z1,z2,z178,z4,z5]),(0,[z1,z2,z3,z1154,z132,z5]),(0,[z6,z1,z2,z3,z4,z1386]),(0,[z110,z1,z2,z3,z4,z38]),(0,[z1387,z1,z2,z3,z4,z5])],[(0,[z1388,z6,z1,z2,z3,z4]),(0,[z12,z1,z468,z3,z4,z5]),(0,[z12,z1,z2,z3,z93,z96]),(0,[z6,z1,z2,z3,z4,z9]),(0,[z98,z1,z2,z3,z4,z66]),(0,[z1389,z1,z2,z3,z4,z5])],[(0,[z6,z1,z2,z3,z4,z1390]),(0,[z6,z1,z1391,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z1392])],[(0,[z1,z42,z2,z388,z4,z5]),(0,[z1,z42,z2,z1157,z4,z5]),(0,[z6,z1,z2,z3,z4,z1393]),(0,[z12,z1,z2,z3,z4,z940]),(0,[z26,z1,z2,z3,z4,z214]),(0,[z6,z1,z2,z388,z132,z5]),(0,[z1,z2,z3,z4,z1394,z5])],[(0,[z1,z1395,z2,z3,z4,z5]),(0,[z288,z1,z2,z3,z4,z347]),(0,[z1396,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z1397,z4,z5]),(0,[z436,z159,z2,z3,z4,z66]),(0,[z278,z1,z2,z3,z4,z66]),(0,[z801,z1,z2,z3,z4,z5])],[(0,[z1,z2,z65,z25,z4,z17]),(0,[z24,z256,z2,z3,z4,z38]),(0,[z1398,z1,z2,z3,z4,z5])],[(0,[z106,z45,z1,z2,z3,z4]),(0,[z459,z139,z2,z3,z4,z5]),(0,[z1,z2,z3,z25,z4,z167]),(0,[z376,z1,z2,z3,z93,z5]),(0,[z6,z484,z2,z3,z4,z38]),(0,[z6,z1,z125,z3,z4,z51])],[(0,[z1399,z6,z1,z2,z3,z4])],[(0,[z1,z2,z3,z170,z4,z5]),(0,[z1,z2,z3,z4,z5,z1400]),(0,[z106,z6,z1,z2,z50,z69])]],
   [[(0,[z42,z2,z3,z4,z66,z38]),(0,[z1,z2,z3,z1153,z4,z5]),(0,[z79,z1,z27,z3,z4,z5]),(0,[z766,z1,z3,z25,z4,z5]),(0,[z6,z1,z2,z1401,z4,z5]),(0,[z1402,z1,z2,z3,z4,z5])],[(0,[z1,z42,z2,z3,z4,z5]),(0,[z1,z2,z339,z25,z4,z5]),(0,[z6,z1,z2,z3,z132,z5]),(0,[z6,z1,z2,z339,z49,z5])],[(0,[z45,z1,z2,z3,z4,z38]),(0,[z12,z1,z2,z3,z4,z214]),(0,[z126,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1403]),(0,[z6,z1,z77,z178,z4,z5]),(0,[z6,z1,z125,z3,z4,z66]),(0,[z6,z1,z52,z792,z4,z5]),(0,[z6,z1,z2,z1404,z4,z5]),(0,[z1405,z1,z2,z3,z4,z5])],[(0,[z291,z1,z2,z604,z4,z5]),(0,[z6,z1,z1406,z3,z4,z5]),(0,[z147,z1,z2,z3,z4,z309]),(0,[z131,z1,z2,z3,z4,z66])],[(0,[z42,z2,z3,z4,z5,z657]),(0,[z12,z1,z2,z3,z4,z499]),(0,[z12,z1,z2,z1105,z4,z5]),(0,[z14,z77,z3,z4,z5,z15]),(0,[z1012,z1,z2,z3,z4,z5])],[(0,[z1,z125,z3,z25,z4,z5]),(0,[z1,z2,z3,z1407,z4,z5]),(0,[z1265,z1,z2,z3,z4,z5]),(0,[z6,z1,z1408,z3,z4,z5]),(0,[z2,z3,z4,z437,z38,z48]),(0,[z6,z159,z2,z3,z4,z827]),(0,[z1,z2,z3,z4,z66,z517]),(0,[z6,z231,z2,z3,z4,z66])],[(0,[z1,z42,z2,z3,z4,z7]),(0,[z159,z139,z2,z3,z4,z5]),(0,[z8,z2,z3,z25,z49,z5]),(0,[z164,z2,z3,z4,z5,z15]),(0,[z26,z2,z3,z4,z49,z38]),(0,[z6,z1,z2,z3,z145,z5]),(0,[z377,z6,z2,z68,z4,z5]),(0,[z1409,z1,z2,z3,z4,z5]),(0,[z1,z1410,z2,z3,z4,z5]),(0,[z106,z996,z1,z2,z3,z4])],[(0,[z605,z2,z3,z4,z5,z48]),(0,[z1411,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z817,z5])],[(0,[z1,z1412,z2,z3,z4,z5]),(0,[z26,z1,z2,z3,z4,z179]),(0,[z1413,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z1414,z5]),(0,[z1415,z1,z2,z3,z4,z5])],[(0,[z6,z1,z2,z3,z4,z771]),(0,[z1,z2,z275,z25,z4,z5]),(0,[z1,z2,z3,z4,z5,z1088]),(0,[z6,z1,z146,z3,z4,z66]),(0,[z1,z2,z3,z1416,z4,z5]),(0,[z1,z2,z3,z4,z5,z1417])],[(0,[z1,z2,z3,z289,z4,z5]),(0,[z1418,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z1419]),(0,[z6,z164,z2,z3,z4,z5]),(0,[z436,z1,z2,z3,z4,z38]),(0,[z411,z6,z1,z3,z4,z40]),(0,[z1420,z1,z2,z3,z4,z5])],[(0,[z578,z1,z2,z512,z4,z5]),(0,[z1,z2,z3,z4,z1421,z5]),(0,[z177,z1,z2,z3,z4,z38]),(0,[z6,z1,z2,z1422,z4,z5]),(0,[z1423,z1,z2,z3,z4,z5]),(0,[z6,z28,z2,z3,z11,z66]),(0,[z1,z1424,z2,z3,z4,z5])],[(0,[z6,z1,z2,z3,z1425,z5]),(0,[z92,z2,z3,z4,z421,z5]),(0,[z1,z2,z3,z153,z4,z66]),(0,[z6,z1,z77,z3,z132,z5]),(0,[z6,z1,z2,z1426,z4,z5]),(0,[z1,z2,z3,z4,z5,z1427]),(0,[z6,z1,z62,z275,z4,z5])],[(0,[z1,z42,z327,z3,z4,z5]),(0,[z26,z1,z2,z3,z4,z317]),(0,[z26,z1,z2,z3,z4,z564]),(0,[z1,z2,z3,z4,z66,z522]),(0,[z6,z2,z3,z4,z5,z827]),(0,[z1,z2,z3,z4,z517,z38]),(0,[z76,z1,z146,z3,z4,z5])],[(0,[z6,z1,z2,z3,z4,z1428]),(0,[z1,z2,z3,z25,z4,z182]),(0,[z1,z2,z3,z4,z5,z1103]),(0,[z1429,z6,z1,z2,z3,z4]),(0,[z1430,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z201,z69,z5])],[(0,[z202,z1,z2,z3,z4,z5]),(0,[z1,z59,z2,z3,z4,z66]),(0,[z26,z1,z425,z3,z4,z5]),(0,[z1,z1431,z2,z3,z4,z5]),(0,[z8,z6,z425,z3,z49,z5]),(0,[z6,z2,z10,z3,z49,z38]),(0,[z6,z1,z2,z3,z4,z1432]),(0,[z1433,z1,z2,z3,z4,z5]),(0,[z1,z1434,z2,z3,z4,z5])]],
   [[(0,[z6,z1,z2,z3,z4,z1435]),(0,[z199,z1,z2,z3,z4,z15]),(0,[z1,z2,z3,z4,z182,z15]),(0,[z26,z1,z52,z53,z4,z5])],[(0,[z95,z1,z43,z3,z4,z5]),(0,[z302,z1,z2,z3,z4,z5]),(0,[z128,z1,z3,z4,z5,z197]),(0,[z6,z1,z2,z3,z1436,z5]),(0,[z6,z1,z2,z65,z4,z562])],[(0,[z6,z1,z327,z3,z145,z5]),(0,[z1,z2,z3,z1437,z4,z5]),(0,[z1,z1438,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z96,z968])],[(0,[z1,z468,z3,z25,z4,z5]),(0,[z56,z26,z1,z2,z10,z5])],[(0,[z6,z1,z904,z3,z4,z5]),(0,[z1287,z1,z2,z3,z4,z66]),(0,[z1,z2,z178,z4,z5,z15]),(0,[z1092,z1,z2,z3,z4,z9]),(0,[z428,z2,z3,z4,z49,z38])],[(0,[z12,z1,z2,z3,z4,z461]),(0,[z1,z2,z3,z25,z1008,z5]),(0,[z1439,z1,z2,z3,z4,z5]),(0,[z348,z1,z2,z3,z4,z38]),(0,[z1,z2,z3,z1290,z4,z66]),(0,[z6,z1440,z2,z3,z4,z5])],[(0,[z147,z1,z42,z2,z3,z122]),(0,[z256,z59,z2,z3,z4,z5]),(0,[z12,z1,z1136,z3,z4,z5]),(0,[z6,z1,z125,z3,z120,z5]),(0,[z1,z2,z3,z491,z4,z38])],[(0,[z12,z1,z425,z3,z4,z5]),(0,[z1441,z1,z2,z3,z4,z5]),(0,[z74,z1,z2,z3,z1008,z5]),(0,[z1,z2,z3,z4,z5,z1442]),(0,[z26,z1,z2,z388,z4,z5]),(0,[z6,z159,z2,z3,z4,z214]),(0,[z1443,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z4,z5,z727]),(0,[z6,z1,z62,z286,z4,z5])],[(0,[z92,z2,z3,z4,z5,z437]),(0,[z24,z2,z3,z25,z4,z38]),(0,[z1,z2,z3,z4,z15,z555]),(0,[z1356,z1,z2,z3,z4,z5]),(0,[z6,z276,z2,z3,z4,z66]),(0,[z1,z2,z3,z4,z214,z719])],[(0,[z1,z32,z2,z3,z4,z167])],[(0,[z1,z784,z2,z3,z4,z5]),(0,[z1444,z1,z2,z3,z4,z5]),(0,[z12,z1,z2,z997,z4,z5]),(1,[z139,z2,z3,z4,z38]),(0,[z1,z2,z3,z4,z1445,z5]),(0,[z1446,z1,z2,z3,z4,z5])],[(0,[z45,z92,z2,z3,z4,z38]),(0,[z1447,z1,z2,z3,z4,z5])],[(0,[z6,z1,z2,z3,z4,z1448]),(0,[z411,z1,z2,z3,z25,z4]),(0,[z1449,z1,z2,z3,z4,z5]),(0,[z1450,z1,z2,z3,z4,z5])],[(0,[z12,z1,z2,z3,z542,z5]),(0,[z2,z3,z11,z4,z421,z5]),(0,[z26,z1,z62,z3,z4,z5]),(0,[z6,z1451,z2,z3,z4,z5])],[(0,[z45,z594,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z1452]),(0,[z8,z2,z3,z235,z49,z5]),(0,[z6,z1,z2,z3,z4,z1453])],[(0,[z12,z1,z2,z388,z4,z5]),(0,[z1,z62,z3,z25,z4,z5]),(0,[z6,z160,z2,z3,z4,z38]),(0,[z1,z2,z3,z1454,z4,z5]),(0,[z6,z1,z2,z3,z93,z968])]],
   [[(0,[z129,z1,z42,z221,z4,z5]),(0,[z1,z2,z3,z4,z5,z1455]),(0,[z6,z1,z804,z3,z4,z5]),(0,[z2,z3,z4,z421,z5,z38]),(0,[z6,z1,z2,z3,z4,z1456])],[(0,[z1,z2,z3,z187,z4,z66]),(0,[z261,z42,z2,z3,z4,z5]),(0,[z6,z823,z2,z3,z4,z5]),(0,[z6,z301,z2,z3,z4,z66]),(0,[z141,z6,z2,z68,z4,z66])],[(0,[z1457,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z1458]),(0,[z191,z1,z2,z3,z4,z66]),(0,[z1,z2,z3,z1459,z4,z5])],[(0,[z1460,z1,z2,z3,z4,z5])],[(0,[z45,z1,z2,z3,z4,z211]),(0,[z42,z2,z3,z4,z49,z38]),(0,[z6,z1,z2,z3,z4,z1461]),(0,[z6,z1462,z2,z3,z4,z5])],[(0,[z6,z1,z2,z1463,z4,z5])],[(0,[z12,z1,z2,z3,z4,z5]),(0,[z315,z1,z2,z3,z4,z5]),(0,[z6,z346,z2,z3,z4,z38]),(0,[z26,z1,z2,z3,z4,z460]),(0,[z1,z2,z3,z4,z5,z975])],[(0,[z19,z42,z2,z3,z4,z38]),(0,[z73,z1,z2,z44,z4,z66]),(0,[z1,z2,z3,z4,z66,z858]),(0,[z6,z1,z2,z3,z4,z1464])],[(0,[z86,z1,z42,z3,z4,z40]),(0,[z1,z2,z3,z4,z1465,z5]),(0,[z6,z1,z837,z3,z4,z5]),(0,[z6,z2,z3,z4,z38,z453])],[(0,[z642,z1,z118,z3,z4,z5]),(0,[z1466,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z178,z4,z461]),(0,[z6,z1,z1467,z3,z4,z5])],[(0,[z1,z42,z2,z3,z4,z108]),(0,[z26,z1,z327,z3,z4,z5]),(0,[z1372,z1,z2,z3,z4,z158]),(0,[z6,z1,z2,z339,z4,z182])],[(0,[z1,z42,z2,z3,z4,z413]),(0,[z45,z608,z2,z3,z4,z5]),(0,[z12,z1,z2,z3,z4,z7]),(0,[z1,z2,z50,z69,z5,z15]),(0,[z159,z59,z2,z3,z4,z5]),(0,[z6,z2,z3,z49,z357,z38]),(0,[z6,z1,z2,z3,z4,z1468])],[(0,[z6,z387,z2,z3,z4,z38]),(0,[z1469,z1,z2,z3,z4,z5])],[(0,[z1,z414,z2,z3,z25,z5]),(0,[z1470,z1,z2,z3,z4,z5])],[(0,[z39,z1,z42,z3,z114,z5]),(0,[z45,z484,z2,z3,z4,z5]),(0,[z80,z55,z3,z25,z4,z5]),(0,[z1,z2,z3,z1471,z4,z5]),(0,[z6,z2,z3,z4,z5,z1472])],[(0,[z6,z784,z2,z3,z4,z5]),(0,[z26,z1,z2,z3,z4,z447]),(0,[z451,z6,z55,z3,z4,z5]),(0,[z6,z1,z2,z3,z1473,z5]),(0,[z110,z1,z2,z3,z4,z179]),(0,[z1,z2,z3,z4,z1474,z5])]],
   [[(0,[z6,z1,z2,z1475,z4,z5])],[(0,[z1476,z1,z2,z3,z4,z5]),(0,[z129,z6,z1,z221,z4,z38]),(0,[z1477,z1,z2,z3,z4,z5]),(0,[z278,z164,z2,z3,z4,z5])],[(0,[z6,z1,z2,z3,z4,z1478]),(0,[z12,z1,z327,z3,z4,z5]),(0,[z6,z1,z2,z310,z4,z9]),(0,[z1479,z1,z2,z3,z4,z5]),(0,[z1330,z1,z2,z3,z4,z66]),(0,[z6,z1,z2,z3,z4,z1480]),(0,[z1,z2,z3,z4,z5,z1481]),(0,[z493,z1,z2,z65,z4,z17])],[(0,[z1,z42,z2,z3,z4,z63]),(0,[z1482,z1,z2,z3,z4,z5]),(0,[z1483,z1,z2,z3,z4,z5]),(0,[z12,z1,z2,z3,z247,z5]),(0,[z129,z1,z221,z25,z4,z5]),(0,[z6,z1,z2,z3,z132,z461]),(0,[z76,z1,z2,z3,z4,z66])],[(0,[z1,z2,z3,z25,z4,z707]),(0,[z1333,z1,z2,z3,z4,z66]),(0,[z1484,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1485])],[(0,[z1,z540,z2,z44,z4,z5]),(0,[z1,z2,z3,z4,z15,z413]),(0,[z1486,z1,z2,z3,z4,z5]),(0,[z141,z6,z2,z68,z120,z5]),(0,[z1,z2,z3,z4,z5,z1487])],[(0,[z298,z42,z2,z3,z4,z5]),(0,[z45,z159,z2,z3,z4,z66]),(0,[z321,z1,z2,z3,z4,z522]),(0,[z1,z427,z2,z3,z4,z391]),(0,[z1488,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1489]),(0,[z1490,z1,z2,z3,z4,z5]),(0,[z325,z1,z2,z3,z4,z447])],[(0,[z8,z45,z2,z3,z49,z5]),(0,[z1,z2,z3,z4,z108,z15]),(0,[z607,z1,z2,z3,z4,z15]),(0,[z141,z6,z2,z948,z4,z5]),(0,[z1,z1491,z2,z3,z4,z5])],[(0,[z1,z2,z3,z25,z4,z38])],[(0,[z6,z1,z2,z3,z4,z1492]),(0,[z1,z2,z3,z4,z66,z309]),(0,[z199,z1,z2,z3,z4,z217])],[(0,[z1,z2,z3,z4,z5,z1005]),(0,[z6,z1,z2,z4,z66,z1028])],[(0,[z1,z42,z2,z310,z4,z5]),(0,[z6,z1,z678,z3,z119,z5]),(0,[z1493,z1,z2,z3,z4,z5]),(0,[z1,z1494,z2,z3,z4,z5])],[(0,[z1495,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z345,z38]),(0,[z6,z1,z1344,z3,z4,z66]),(0,[z1,z1496,z2,z3,z4,z5])],[(0,[z1497,z1,z2,z3,z4,z5]),(0,[z1038,z1,z2,z3,z4,z182]),(0,[z56,z6,z1,z2,z10,z66]),(0,[z1498,z1,z2,z3,z4,z5])],[(0,[z12,z1,z2,z3,z406,z5]),(0,[z6,z1,z2,z3,z120,z51]),(0,[z949,z1,z2,z3,z4,z38]),(0,[z6,z1,z2,z369,z4,z17]),(0,[z1,z2,z3,z4,z5,z1499]),(0,[z6,z1,z2,z921,z50,z5]),(0,[z6,z1,z1500,z3,z4,z5])],[(0,[z1,z1501,z2,z3,z4,z5]),(0,[z26,z1,z2,z3,z4,z499]),(0,[z73,z1,z2,z745,z4,z5]),(0,[z1,z2,z3,z1502,z4,z5]),(0,[z1,z2,z3,z25,z4,z738]),(0,[z1,z2,z3,z318,z5,z15]),(0,[z39,z6,z1,z3,z114,z38]),(0,[z598,z6,z2,z3,z4,z38]),(0,[z6,z164,z146,z3,z4,z5])]],
   [[(0,[z234,z1,z2,z3,z4,z66]),(0,[z1503,z1,z2,z3,z4,z5])],[(0,[z1,z327,z3,z4,z5,z15]),(0,[z1,z2,z3,z4,z5,z1504]),(0,[z6,z261,z2,z3,z4,z156])],[(0,[z42,z2,z23,z3,z4,z5]),(0,[z45,z1,z2,z339,z4,z5]),(0,[z1505,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z1506,z4,z5]),(0,[z6,z261,z62,z3,z4,z5])],[(0,[z1,z2,z44,z745,z4,z5]),(0,[z1,z2,z3,z4,z5,z279]),(0,[z1,z2,z3,z4,z51,z15]),(0,[z6,z1,z2,z3,z120,z66]),(0,[z6,z261,z2,z3,z4,z5]),(0,[z6,z1,z2,z369,z4,z338])],[(0,[z8,z12,z2,z3,z49,z5]),(0,[z1,z2,z3,z4,z1507,z5]),(0,[z2,z3,z4,z49,z38,z48])],[(0,[z1,z366,z2,z3,z4,z5]),(0,[z79,z1,z118,z3,z4,z5]),(0,[z866,z1,z2,z3,z4,z66]),(0,[z6,z1,z1508,z3,z4,z5]),(0,[z1509,z1,z2,z3,z4,z5])],[(0,[z19,z139,z2,z3,z4,z5]),(0,[z6,z2,z3,z4,z66,z657]),(0,[z202,z28,z2,z3,z11,z5])],[(0,[z80,z177,z55,z3,z4,z5]),(0,[z39,z232,z1,z3,z114,z5])],[(0,[z1,z2,z3,z153,z4,z522]),(0,[z1510,z1,z2,z3,z4,z5])],[(0,[z19,z42,z2,z3,z4,z211]),(0,[z24,z45,z2,z3,z4,z38]),(0,[z12,z1,z2,z1242,z4,z5]),(0,[z1,z2,z3,z4,z5,z1511]),(0,[z1512,z1,z2,z3,z4,z5])],[(0,[z6,z1,z2,z898,z4,z5]),(0,[z1,z2,z3,z4,z5,z1041]),(0,[z1288,z1,z2,z3,z4,z5])],[(0,[z6,z1,z2,z3,z1513,z5]),(0,[z80,z42,z55,z3,z4,z5]),(0,[z419,z1,z2,z46,z4,z5]),(0,[z313,z1,z2,z3,z4,z15]),(0,[z6,z901,z2,z3,z4,z5]),(0,[z12,z1,z2,z3,z25,z5]),(0,[z493,z1,z2,z3,z4,z38]),(0,[z1514,z1,z2,z3,z4,z5])],[(0,[z1,z42,z99,z3,z4,z116]),(0,[z6,z1,z2,z1515,z4,z5]),(0,[z6,z1,z2,z948,z4,z5])],[(0,[z1015,z1,z42,z3,z4,z5]),(0,[z1,z2,z44,z4,z572,z5]),(0,[z376,z1,z2,z3,z4,z5]),(0,[z1516,z1,z2,z3,z4,z5]),(0,[z6,z1,z468,z3,z4,z182]),(1,[z6,z2,z3,z4,z827]),(0,[z6,z2,z3,z628,z4,z38]),(0,[z106,z6,z1,z2,z286,z4])],[(0,[z419,z1,z2,z282,z4,z5]),(0,[z1,z2,z3,z1517,z4,z5]),(0,[z130,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z685,z15]),(0,[z1,z2,z3,z4,z370,z38])],[(0,[z12,z1,z2,z3,z4,z108]),(0,[z1518,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z1519,z5]),(0,[z1520,z1,z2,z3,z4,z5]),(0,[z735,z1,z2,z3,z4,z5]),(0,[z1,z1521,z2,z3,z4,z5]),(1,[z6,z1,z2,z921,z5])]],
   [[(0,[z26,z1,z2,z3,z4,z63]),(0,[z12,z1,z2,z3,z4,z413]),(0,[z26,z1,z2,z3,z4,z461]),(0,[z1,z1522,z2,z3,z4,z5]),(0,[z6,z1,z2,z275,z4,z5]),(0,[z6,z1523,z2,z3,z4,z5])],[(0,[z1,z2,z3,z157,z4,z66]),(0,[z1524,z1,z2,z3,z4,z5])],[(0,[z1,z2,z514,z4,z572,z5]),(0,[z26,z28,z2,z3,z4,z38]),(0,[z6,z1,z2,z178,z4,z66]),(0,[z6,z1,z2,z1525,z4,z5]),(0,[z30,z6,z2,z3,z4,z38])],[(0,[z141,z6,z2,z68,z145,z5]),(0,[z1,z2,z3,z4,z5,z1526]),(0,[z1527,z1,z2,z3,z4,z5]),(0,[z6,z1,z195,z3,z4,z397]),(0,[z1528,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z309,z38]),(0,[z531,z2,z3,z4,z5,z437]),(0,[z6,z1,z2,z339,z4,z38]),(0,[z6,z1,z52,z53,z4,z38])],[(0,[z12,z1254,z2,z3,z4,z5]),(0,[z1529,z1,z2,z3,z4,z5]),(0,[z348,z1,z2,z339,z4,z5])],[(0,[z6,z1,z1064,z3,z4,z5]),(0,[z12,z39,z1,z3,z114,z5]),(0,[z387,z2,z3,z187,z4,z5]),(0,[z807,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z1397,z4,z66])],[(0,[z1,z42,z2,z3,z4,z51]),(0,[z1,z2,z3,z91,z49,z5]),(0,[z45,z2,z3,z4,z66,z38]),(0,[z45,z346,z2,z3,z4,z5]),(0,[z74,z1,z2,z3,z170,z5]),(0,[z1,z1530,z3,z25,z4,z5]),(0,[z1531,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z339,z11,z5]),(0,[z6,z1,z2,z3,z4,z964]),(0,[z288,z1,z2,z3,z93,z96])],[(0,[z12,z1,z2,z3,z4,z63]),(0,[z315,z1,z2,z3,z4,z63]),(0,[z1,z2,z3,z4,z5,z1532]),(0,[z6,z1,z2,z3,z4,z1533]),(0,[z1,z146,z3,z25,z4,z5]),(0,[z26,z1,z2,z310,z4,z5]),(0,[z106,z26,z1,z2,z3,z4]),(0,[z8,z6,z2,z310,z49,z5]),(0,[z6,z1,z2,z50,z69,z38])],[(0,[z164,z42,z2,z3,z4,z5]),(0,[z86,z1,z3,z25,z4,z40]),(0,[z1,z2,z3,z4,z5,z1084]),(0,[z6,z1,z2,z3,z4,z1534]),(0,[z1,z2,z3,z1535,z4,z5]),(0,[z1309,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z25,z4,z211]),(0,[z6,z1,z2,z3,z1536,z5]),(0,[z12,z28,z2,z3,z4,z38]),(0,[z1,z2,z3,z4,z5,z370]),(0,[z1,z2,z3,z170,z4,z66]),(0,[z6,z1,z485,z3,z119,z5])],[(0,[z45,z1,z2,z3,z4,z391]),(0,[z6,z1,z1348,z3,z4,z5]),(0,[z12,z1,z146,z3,z4,z5]),(0,[z6,z1,z1530,z3,z4,z5]),(0,[z431,z1,z2,z3,z4,z179]),(0,[z6,z1537,z2,z3,z4,z5]),(0,[z6,z1,z2,z286,z4,z5])],[(0,[z1,z42,z2,z3,z4,z66]),(0,[z1538,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z132,z66]),(0,[z6,z1,z2,z3,z145,z51]),(0,[z226,z1,z2,z3,z4,z38]),(0,[z1202,z1,z2,z3,z4,z5])],[(0,[z1539,z1,z2,z3,z4,z5]),(0,[z12,z28,z2,z3,z11,z5]),(0,[z1,z1030,z3,z25,z4,z5]),(0,[z1,z2,z3,z153,z4,z242]),(0,[z6,z1,z3,z4,z5,z1253]),(0,[z126,z1,z2,z3,z4,z66]),(1,[z6,z1,z2,z3,z968])],[(0,[z1,z2,z3,z4,z235,z5]),(0,[z1,z2,z3,z4,z15,z676]),(0,[z1,z2,z3,z4,z1540,z5]),(0,[z177,z1,z2,z3,z318,z5]),(0,[z24,z2,z3,z4,z38,z48]),(0,[z6,z2,z3,z645,z4,z38]),(0,[z1541,z1,z2,z3,z4,z5])],[(0,[z1542,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z1543]),(0,[z74,z1,z2,z3,z25,z38]),(0,[z1,z2,z3,z4,z15,z522]),(0,[z70,z1,z2,z3,z4,z38])]],
   [[(0,[z1,z2,z3,z4,z5,z317]),(0,[z1,z395,z2,z3,z4,z148]),(0,[z322,z42,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z108,z217]),(0,[z12,z1,z2,z310,z4,z5]),(0,[z6,z1,z1408,z3,z4,z66]),(0,[z1,z1544,z2,z3,z4,z5])],[(0,[z26,z1,z2,z3,z4,z5]),(0,[z155,z42,z2,z3,z4,z5]),(0,[z344,z1,z71,z3,z4,z5]),(0,[z1,z2,z3,z4,z179,z15]),(0,[z1,z2,z3,z4,z7,z15]),(0,[z6,z1,z2,z3,z145,z66]),(0,[z8,z6,z2,z3,z49,z5]),(0,[z6,z1,z62,z3,z4,z38])],[(0,[z2,z3,z187,z4,z421,z5]),(0,[z1,z2,z44,z4,z5,z100]),(0,[z451,z6,z2,z3,z4,z38]),(0,[z1411,z1,z2,z3,z4,z66]),(0,[z39,z191,z1,z3,z114,z5]),(0,[z6,z1,z2,z3,z5,z968]),(0,[z1545,z1,z2,z3,z4,z5])],[(0,[z234,z1,z2,z3,z4,z158]),(0,[z6,z227,z2,z3,z4,z38]),(0,[z1546,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1547]),(0,[z1,z2,z3,z4,z1548,z5]),(0,[z133,z1,z2,z3,z4,z182]),(0,[z86,z229,z1,z3,z4,z40]),(0,[z1549,z1,z2,z3,z4,z5])],[(0,[z1,z1550,z2,z3,z4,z5]),(0,[z1551,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z289,z4,z66]),(0,[z6,z164,z2,z3,z4,z66])],[(0,[z26,z1,z2,z3,z4,z7]),(0,[z41,z6,z261,z2,z3,z4])],[(0,[z1,z1552,z2,z3,z4,z5]),(0,[z1,z2,z3,z91,z4,z38]),(0,[z1,z2,z3,z4,z5,z345]),(0,[z6,z1,z2,z3,z318,z38]),(0,[z902,z1,z2,z3,z4,z38])],[(0,[z325,z1,z2,z3,z4,z5]),(0,[z1,z1553,z2,z3,z4,z5]),(0,[z26,z1,z2,z3,z4,z437]),(0,[z6,z1,z2,z68,z145,z5])],[(0,[z6,z1,z953,z3,z4,z5]),(0,[z1021,z1,z2,z3,z4,z5]),(0,[z26,z1,z99,z3,z4,z116]),(0,[z575,z1,z2,z3,z4,z38]),(0,[z6,z1,z209,z3,z119,z5]),(0,[z76,z164,z2,z3,z4,z5])],[(0,[z268,z1,z2,z3,z4,z5]),(0,[z202,z1,z2,z3,z4,z66]),(0,[z1,z2,z3,z4,z317,z38]),(0,[z12,z1,z2,z3,z613,z5]),(0,[z6,z1,z2,z3,z4,z167]),(0,[z6,z1,z2,z3,z4,z1554]),(0,[z1,z2,z3,z1555,z4,z5]),(0,[z278,z261,z2,z3,z4,z5])],[(0,[z515,z42,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z1556,z5]),(0,[z1557,z1,z2,z3,z4,z5]),(0,[z411,z6,z1,z99,z3,z4]),(0,[z41,z131,z1,z2,z4,z18])],[(0,[z6,z1,z425,z3,z4,z182]),(0,[z302,z1,z2,z3,z4,z66])],[(0,[z1,z2,z3,z4,z63,z15]),(0,[z1,z42,z2,z3,z4,z109]),(0,[z1,z1558,z2,z3,z4,z5]),(0,[z234,z1,z2,z3,z132,z5]),(0,[z1559,z1,z2,z3,z4,z5])],[(0,[z1,z427,z2,z3,z4,z5]),(0,[z1560,z1,z2,z3,z4,z5])],[(0,[z6,z1,z2,z3,z4,z1561]),(0,[z6,z1,z2,z525,z69,z5]),(0,[z1562,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z968])]],
   [[(0,[z6,z1,z2,z3,z4,z1563]),(0,[z1,z42,z2,z3,z120,z5]),(0,[z138,z1,z2,z4,z5,z75]),(0,[z1564,z1,z2,z3,z4,z5])],[(0,[z1,z42,z2,z3,z4,z82]),(0,[z6,z1,z2,z3,z4,z970]),(0,[z12,z1,z99,z3,z4,z116])],[(0,[z1,z42,z125,z3,z4,z5]),(0,[z376,z1,z2,z3,z25,z5]),(0,[z6,z1,z2,z1117,z4,z5]),(0,[z6,z1,z99,z3,z4,z416]),(0,[z1565,z1,z2,z3,z4,z5])],[(0,[z6,z2,z3,z817,z49,z5]),(0,[z6,z1,z399,z3,z119,z5]),(0,[z24,z6,z2,z3,z4,z38]),(0,[z6,z1,z1566,z3,z4,z5])],[(0,[z1,z2,z3,z1567,z4,z5]),(0,[z26,z1,z2,z3,z4,z51]),(0,[z313,z1,z2,z3,z4,z217]),(0,[z1,z1568,z2,z3,z4,z5])],[(0,[z1,z1569,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z1570]),(0,[z1,z2,z3,z4,z82,z15]),(0,[z6,z1,z2,z178,z4,z158]),(0,[z1571,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z413,z1351]),(0,[z1070,z1,z2,z3,z4,z38]),(0,[z6,z2,z3,z4,z66,z168]),(0,[z6,z1,z2,z3,z4,z1572]),(0,[z1,z1573,z2,z3,z4,z5])],[(0,[z87,z1,z2,z3,z4,z5]),(0,[z324,z2,z3,z4,z421,z5])],[(0,[z1,z2,z3,z1574,z4,z5]),(0,[z6,z1,z2,z1575,z4,z5]),(0,[z6,z1,z125,z3,z145,z5]),(0,[z6,z1,z468,z3,z4,z38]),(0,[z6,z1,z2,z220,z4,z562]),(0,[z278,z1,z2,z275,z4,z5])],[(0,[z543,z1,z2,z3,z175,z5]),(0,[z348,z1,z468,z3,z4,z5])],[(0,[z1,z42,z146,z3,z4,z5]),(0,[z12,z1,z2,z3,z13,z38]),(0,[z2,z3,z4,z66,z217,z38]),(0,[z41,z6,z1,z2,z4,z727]),(0,[z1576,z1,z2,z3,z4,z5])],[(0,[z543,z1,z2,z3,z13,z5]),(0,[z1,z2,z3,z4,z5,z993]),(0,[z1,z2,z3,z289,z4,z82])],[(0,[z1,z2,z3,z4,z211,z15]),(0,[z45,z2,z3,z4,z49,z38]),(0,[z1577,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z182]),(0,[z1578,z1,z2,z3,z4,z5]),(0,[z1579,z1,z2,z3,z4,z5]),(0,[z1,z1580,z2,z3,z4,z5])],[(0,[z6,z1,z2,z990,z4,z5]),(0,[z880,z1,z2,z3,z4,z5]),(0,[z12,z1,z2,z3,z4,z51]),(0,[z147,z1,z2,z3,z25,z122]),(0,[z1581,z1,z2,z3,z4,z5]),(0,[z14,z32,z77,z3,z4,z5])],[(0,[z45,z1,z2,z3,z4,z179]),(0,[z12,z1317,z2,z3,z4,z5]),(0,[z12,z129,z1,z221,z4,z5]),(0,[z6,z1,z1027,z3,z4,z5]),(0,[z431,z1,z327,z3,z4,z5])],[(0,[z1,z2,z3,z4,z38,z48]),(0,[z1,z2,z3,z4,z5,z1582]),(0,[z6,z790,z2,z3,z4,z5]),(0,[z6,z1,z1583,z3,z4,z5])],[(0,[z1,z42,z2,z3,z4,z158]),(0,[z35,z1,z2,z46,z4,z38]),(0,[z6,z1,z2,z3,z132,z158]),(0,[z6,z1,z1584,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z1585])]],
   [[(0,[z276,z42,z2,z3,z4,z5]),(0,[z45,z681,z2,z3,z4,z5]),(0,[z26,z1,z1235,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z1586])],[(0,[z12,z1,z2,z3,z4,z66]),(0,[z411,z1,z2,z3,z4,z15]),(0,[z240,z6,z2,z3,z49,z5]),(0,[z315,z1,z2,z3,z4,z66]),(0,[z6,z102,z2,z3,z4,z38]),(0,[z6,z2,z3,z4,z38,z222]),(0,[z1101,z1,z2,z3,z4,z38]),(0,[z6,z1,z2,z1102,z4,z38]),(0,[z1,z2,z3,z4,z66,z1036]),(0,[z1587,z6,z1,z2,z3,z4]),(0,[z302,z1,z2,z3,z4,z82])],[(0,[z1,z88,z3,z297,z4,z5]),(0,[z695,z1,z2,z3,z4,z15]),(0,[z6,z1,z2,z3,z1008,z5]),(1,[z59,z2,z3,z4,z38]),(0,[z6,z1,z2,z3,z1588,z5]),(0,[z6,z1,z2,z3,z1589,z5]),(0,[z278,z1,z2,z286,z4,z5])],[(0,[z42,z2,z3,z194,z4,z5]),(0,[z1,z2,z3,z153,z5,z151])],[(0,[z1,z2,z3,z4,z124,z15]),(0,[z1,z2,z3,z4,z5,z1590]),(0,[z6,z1,z3,z114,z750,z5])],[(0,[z45,z1,z52,z53,z4,z5]),(0,[z288,z1,z2,z3,z4,z5]),(0,[z6,z77,z1027,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z1591]),(0,[z6,z1,z2,z1592,z4,z5]),(0,[z1,z1593,z2,z3,z4,z5]),(0,[z6,z1,z1594,z3,z4,z5]),(0,[z6,z1,z146,z275,z4,z5])],[(0,[z1,z2,z3,z25,z476,z5]),(0,[z1,z1299,z3,z25,z4,z5]),(0,[z6,z1,z1208,z3,z4,z5]),(0,[z6,z1,z425,z3,z49,z5]),(0,[z1595,z1,z2,z3,z4,z5]),(0,[z6,z1,z53,z792,z4,z5])],[(0,[z6,z1,z2,z3,z4,z1596]),(0,[z1597,z1,z2,z3,z4,z5]),(0,[z6,z650,z2,z3,z4,z38]),(0,[z1598,z1,z2,z3,z4,z5]),(0,[z1599,z1,z2,z3,z4,z5])],[(0,[z73,z1,z2,z554,z4,z5]),(0,[z6,z1,z2,z3,z4,z1025]),(0,[z6,z438,z2,z3,z4,z66])],[(0,[z45,z1,z2,z50,z69,z5]),(0,[z1,z2,z3,z4,z1600,z5]),(0,[z1601,z1,z2,z3,z4,z5]),(0,[z171,z1,z2,z3,z4,z38]),(0,[z6,z1,z2,z3,z4,z727]),(0,[z1602,z1,z2,z3,z4,z5])],[(0,[z26,z1,z2,z3,z4,z108]),(0,[z26,z1,z2,z3,z4,z109]),(0,[z1603,z6,z1,z2,z3,z4]),(0,[z1604,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z1605])],[(0,[z1,z2,z3,z25,z318,z5]),(0,[z26,z1,z2,z3,z4,z413]),(0,[z1606,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z1475,z4,z66]),(0,[z6,z1,z2,z1607,z4,z5]),(0,[z6,z1,z2,z3,z4,z781])],[(0,[z1608,z1,z2,z3,z4,z5]),(0,[z6,z1,z3,z4,z781,z40]),(0,[z6,z1,z2,z65,z4,z17])],[(0,[z1,z2,z3,z4,z309,z40]),(0,[z8,z2,z3,z4,z421,z5]),(0,[z1,z2,z65,z4,z17,z15]),(0,[z1609,z1,z2,z3,z4,z5])],[(0,[z6,z1027,z55,z3,z4,z5]),(0,[z133,z1,z2,z3,z4,z38]),(0,[z6,z2,z3,z4,z143,z38]),(0,[z163,z6,z1,z3,z4,z246]),(0,[z6,z1,z2,z3,z4,z1610]),(0,[z1611,z1,z2,z3,z4,z5])],[(0,[z287,z1,z2,z272,z4,z5]),(0,[z1,z2,z3,z1612,z4,z5]),(0,[z26,z1,z2,z1364,z4,z5]),(0,[z26,z1,z125,z3,z4,z5]),(0,[z1,z2,z3,z4,z1613,z5]),(0,[z1614,z1,z2,z3,z4,z5])]],
   [[(0,[z73,z1,z2,z253,z4,z5]),(0,[z1,z2,z3,z4,z5,z1615]),(0,[z6,z2,z3,z114,z49,z38]),(0,[z210,z1,z2,z3,z4,z38]),(0,[z1616,z1,z2,z3,z4,z5])],[(0,[z387,z42,z2,z3,z4,z5]),(0,[z1,z2,z3,z25,z4,z391]),(0,[z1,z2,z3,z25,z4,z917]),(0,[z6,z14,z77,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1190]),(0,[z6,z1,z2,z1617,z4,z5]),(0,[z1,z1618,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1619]),(0,[z45,z1,z62,z3,z4,z5]),(0,[z1,z2,z3,z4,z15,z664]),(0,[z12,z1,z2,z3,z4,z109]),(0,[z8,z26,z2,z3,z49,z5]),(0,[z1620,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z3,z93,z602])],[(0,[z134,z6,z2,z3,z4,z38]),(0,[z6,z1,z2,z1134,z4,z38]),(0,[z1621,z1,z2,z3,z4,z5]),(0,[z164,z1494,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1622]),(0,[z6,z1,z2,z3,z4,z1623]),(0,[z1,z2,z3,z536,z25,z5]),(0,[z1624,z1,z2,z3,z4,z5]),(0,[z1,z1625,z2,z3,z4,z5]),(0,[z110,z1,z327,z3,z4,z5]),(0,[z647,z6,z1,z221,z4,z5]),(0,[z6,z1,z1626,z3,z4,z5]),(0,[z147,z6,z1,z2,z3,z453])],[(0,[z1272,z6,z1,z2,z4,z5]),(0,[z14,z139,z2,z3,z4,z5]),(0,[z12,z1,z2,z3,z120,z5]),(0,[z6,z169,z2,z3,z4,z66]),(0,[z177,z1,z2,z388,z4,z5])],[(0,[z12,z1,z2,z3,z4,z82]),(0,[z26,z1,z146,z3,z4,z5]),(0,[z6,z1,z425,z3,z4,z38]),(0,[z6,z1,z2,z10,z921,z5])],[(0,[z6,z1,z2,z3,z4,z1627]),(0,[z12,z1,z125,z3,z4,z5]),(0,[z1,z32,z2,z3,z4,z38]),(0,[z348,z1,z425,z3,z4,z5]),(0,[z1628,z1,z2,z3,z4,z5]),(0,[z6,z1,z2,z921,z69,z5])],[(0,[z42,z2,z225,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1629]),(0,[z45,z1,z2,z3,z318,z5]),(0,[z6,z1,z2,z3,z1630,z5]),(0,[z1277,z2,z3,z25,z4,z5]),(0,[z26,z28,z2,z3,z11,z5]),(0,[z6,z1,z2,z593,z69,z5]),(0,[z1,z2,z3,z4,z66,z1086])],[(0,[z6,z1,z2,z3,z4,z1631]),(0,[z6,z1,z425,z3,z11,z5]),(0,[z86,z6,z1,z146,z3,z4]),(0,[z1,z2,z3,z4,z5,z1632])],[(0,[z6,z1,z2,z3,z4,z1633]),(0,[z80,z6,z55,z3,z4,z38]),(0,[z1634,z1,z2,z3,z4,z5])],[(0,[z127,z1,z218,z3,z4,z5]),(0,[z6,z457,z2,z3,z4,z66]),(0,[z411,z6,z1,z2,z3,z4]),(0,[z1420,z164,z2,z3,z4,z5])],[(0,[z177,z1,z2,z3,z4,z5]),(0,[z26,z1,z2,z3,z4,z158]),(0,[z1,z2,z3,z4,z5,z1635]),(0,[z6,z1,z2,z3,z4,z1636])],[(0,[z6,z1,z2,z1637,z4,z5]),(0,[z1638,z1,z2,z3,z4,z5]),(0,[z1312,z1,z2,z3,z4,z5]),(0,[z6,z2,z3,z4,z66,z104]),(0,[z1,z2,z3,z4,z1639,z5]),(0,[z6,z1,z3,z4,z5,z781])],[(0,[z26,z1,z2,z3,z4,z309]),(0,[z1,z2,z3,z1640,z4,z5]),(0,[z6,z1,z2,z388,z4,z38]),(0,[z256,z1,z2,z3,z4,z48]),(0,[z6,z261,z2,z3,z4,z66])],[(0,[z1,z1641,z2,z3,z4,z5])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 480) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 480).take 469) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 949).take 474) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1423).take 300) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1723)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [480, 469, 474, 300] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 103).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 103).take 103).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 206).take 101).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 307).take 97).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 404).take 101).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc5 : chunkOK 5 ((bkB.flatten.drop 505).take 7).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [103, 103, 101, 97, 101, 7] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_cons pc5 (windowsF_nil pcend))))))

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

end PEqualNP.Outside.L_meta_37501

theorem PEqualNP.Outside.L_meta_37501 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4276808904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809448 * 2 ^ 32 + 4276808904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_37501.solve