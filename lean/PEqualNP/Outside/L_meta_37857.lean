import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_37857

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
  Nat.testBit (4277074664 * 2 ^ 32 + 4274833608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0xa0023418dc0e918a#64 ++ 0xb40046831b81d231#64 ++ 0xd8167479fc1e939b#64 ++ 0xfb02ce8f3f83d273#64 : BitVec 256),
   (0x4020884220202630#64 ++ 0x08041108440404c6#64 ++ 0xb86988463063ffff#64 ++ 0xf70d3108c60c7fff#64 : BitVec 256),
   (0x808e05854d8318c3#64 ++ 0xd011c0b0a9b06318#64 ++ 0x778e0f87cf831ce7#64 ++ 0xaef1c1f0f9f0639c#64 : BitVec 256),
   (0x03700ee806f41f04#64 ++ 0xe06e01dd00de83e0#64 ++ 0xfff00ff80ffc1f06#64 ++ 0x9ffe01ff01ff83e0#64 : BitVec 256),
   (0x01df50000b5bc007#64 ++ 0x003bea00016b7800#64 ++ 0xfbfff0000fffe006#64 ++ 0x7f7ffe0001fffc00#64 : BitVec 256),
   (0x05fdeb77b0000000#64 ++ 0x00bfbd6ef6000000#64 ++ 0xf5fffffff0000001#64 ++ 0xfebffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [7, 1]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [3, 11]⟩, ⟨.or, [1, 12]⟩, ⟨.and, [6, 13]⟩, ⟨.or, [10, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0xfbfff0000fffe006 0x7f7ffe0001fffc00

def z1 : W := mkw 0x035006a806d41904 0xe06a00d500da8320 0x479007b80f9c0000 0x08f200f701f38000

def z2 : W := mkw 0x03ff5ee80fffdf07 0xe07febdd01fffbe0 0xfffffff80fffff06 0xffffffff01ffffe0

def z3 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0xf5fffffff0000001 0xfebffffffe000000

def z4 : W := mkw 0x4020884220202630 0x08041108440404c6 0xb86988463063ffff 0xf70d3108c60c7fff

def z5 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0x778e0f87cf831ce7 0xaef1c1f0f9f0639c

def z6 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0xd8167479fc1e939b 0xfb02ce8f3f83d273

def z7 : W := mkw 0x01dd400000000000 0x003ba80000000000 0xf1fff00000000000 0x7e3ffe0000000000

def z8 : W := mkw 0x0000000000000000 0x0000000000000000 0xb86980000063e006 0x770d3000000c7c00

def z9 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0xfff00ff80ffc1f06 0x9ffe01ff01ff83e0

def z10 : W := mkw 0x41ffd8422b7be637 0x083ffb08456f7cc6 0xfbfff8463fffffff 0xff7fff08c7ffffff

def z11 : W := mkw 0x01dd50000258c004 0x003baa00004b1800 0xf9fff000007ce000 0x7f3ffe00000f9c00

def z12 : W := mkw 0x0000000000000000 0x0000000000000000 0x980000403002939b 0xf300000806005273

def z13 : W := mkw 0xe022bc5afc2eb7ba 0xbc04578b5f85d6f7 0xf87ffc7ffc7fffff 0xff0fff8fff8fffff

def z14 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0xfdfffffff063e007 0xffbffffffe0c7c00

def z15 : W := mkw 0x45fdeb77b0202630 0x08bfbd6ef60404c6 0xfdfffffff063ffff 0xffbffffffe0c7fff

def z16 : W := mkw 0xa0002418d4041188 0xb40004831a808231 0x00000479f0001399 0x8000008f3e000273

def z17 : W := mkw 0x05dd633590000000 0x00bbac66b2000000 0x459677b9c0000000 0x08b2cef738000000

def z18 : W := mkw 0xa00214084c0e918a 0xb40042810981d231 0x980000403c1e939b 0xf30000080783d273

def z19 : W := mkw 0x01dd400000000000 0x003ba80000000000 0x4196700000000000 0x0832ce0000000000

def z20 : W := mkw 0x0000201090000000 0x0000040212000000 0xd0167479f0000001 0xfa02ce8f3e000000

def z21 : W := mkw 0x0420ab77b0000000 0x0084156ef6000000 0x04000ffff0000001 0x808001fffe000000

def z22 : W := mkw 0x43708eea26f43f34 0xe86e11dd44de87e6 0xfff98ffe3fffffff 0xffff31ffc7ffffff

def z23 : W := mkw 0x800204004c021082 0x9000408009804210 0x50060401cc021083 0xaa00c08039804210

def z24 : W := mkw 0x0551623090000000 0x00aa2c4612000000 0x0010703800000000 0x00020e0700000000

def z25 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0x40167439cc1c0000 0x0802ce8739838000

def z26 : W := mkw 0x05df73359b5bc007 0x00bbee66b36b7800 0x479677b9cf9c0000 0x08f2cef739f38000

def z27 : W := mkw 0x0000048004801800 0xc000009000900300 0x77800f800f801c06 0x8ef001f001f00380

def z28 : W := mkw 0x0200048806f41f04 0xe040009100de83e0 0xda1004780ffc1f06 0x9b42008f01ff83e0

def z29 : W := mkw 0x0020084000200600 0x00040108000400c0 0xb860084000601f06 0x970c0108000c03e0

def z30 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0x2be980000fffe006 0x057d300001fffc00

def z31 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0xf81e7c7ffc1f9fff 0xff03cf8fff83f3ff

def z32 : W := mkw 0x07fdefffb6f41f04 0xe0ffbdfff6de83e0 0xfffffffffffc1f07 0xffffffffffff83e0

def z33 : W := mkw 0x808e0105490300c3 0x1011c020a9206018 0x000e0007c00300e1 0x2001c000f800601c

def z34 : W := mkw 0xa0023498dc8e998a 0xf40046931b91d331 0xff967ff9ff9e9f9f 0xfff2cfff3ff3d3f3

def z35 : W := mkw 0x81df55854fdbd8c7 0xd03beab0a9fb7b18 0xffffff87cffffce7 0xfffffff0f9ffff9c

def z36 : W := mkw 0x05fdeb77b3514005 0x00bfbd6ef66a2800 0xf7fffffff3e16005 0xfefffffffe7c2c00

def z37 : W := mkw 0x008c010500000000 0x00118020a0000000 0x758e0f87c0000001 0xaeb1c1f0f8000000

def z38 : W := mkw 0x0000040804041100 0xa000008100808220 0xd81004780c1c1302 0x9b02008f01838260

def z39 : W := mkw 0xa3723ef8defe9f8e 0xf46e47df1bdfd3f1 0xfff67ff9fffe9f9f 0xfffecfff3fffd3f3

def z40 : W := mkw 0x008c010500000000 0x00118020a0000000 0x758e0f87c0031ce7 0xaeb1c1f0f800639c

def z41 : W := mkw 0xe020ac5af42437b8 0xbc04158b5e8486f7 0x00000c7ff0001ff9 0x8000018ffe0003ff

def z42 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0xf87ff479fc7ff39f 0xff0ffe8f3f8ffe73

def z43 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0x439670000f9c0000 0x0872ce0001f38000

def z44 : W := mkw 0x4020884220202630 0x08041108440404c6 0x0000084630001ff9 0x80000108c60003ff

def z45 : W := mkw 0x43708eea26f43f34 0xe86e11dd44de87e6 0xfff00ffe3ffc1fff 0x9ffe01ffc7ff83ff

def z46 : W := mkw 0x0020084000200600 0x00040108000400c0 0x2060080000600c04 0x040c0100000c0180

def z47 : W := mkw 0x01df51050b5bc007 0x003bea20a16b7800 0xffffff87cfffe007 0xfffffff0f9fffc00

def z48 : W := mkw 0x0002000008020002 0x0000400001004000 0x500600000c020002 0x2a00c00001804000

def z49 : W := mkw 0x85ffeff7fd8318c3 0xd0bffdfeffb06318 0xf7ffffffff831ce7 0xfefffffffff0639c

def z50 : W := mkw 0xa5ffff7ffc0e918a 0xb4bfffefff81d231 0xfdfffffffc1e939b 0xffbfffffff83d273

def z51 : W := mkw 0x0150000002500004 0x002a0000004a0000 0xfbf000000ffc0006 0x1f7e000001ff8000

def z52 : W := mkw 0x015150000258c004 0x002a2a00004b1800 0x8871f000007ce000 0x510e3e00000f9c00

def z53 : W := mkw 0x05fffb77bb5bc007 0x00bfff6ef76b7800 0xffffffffffffe007 0xfffffffffffffc00

def z54 : W := mkw 0x45fdeb77b0202630 0x08bfbd6ef60404c6 0xf5fffffff0001ff9 0xfebffffffe0003ff

def z55 : W := mkw 0x008e000009030003 0x0011c00001206000 0x738e00000f830006 0x2e71c00001f06000

def z56 : W := mkw 0xa1df7418df5fd18f 0xb43bee831bebfa31 0xfbfff479fffff39f 0xff7ffe8f3ffffe73

def z57 : W := mkw 0x0200008002f00e04 0x40400010005e01c0 0x0200000003e00c04 0x00400000007c0180

def z58 : W := mkw 0xa08e359ddd8f99cb 0xf411c6b3bbb1f339 0xff9e7fffff9f9fff 0xfff3cffffff3f3ff

def z59 : W := mkw 0xa0023010d80a808a 0x140046021b015011 0x98067041f002939b 0xf300ce083e005273

def z60 : W := mkw 0x07fd6ffd96f41f04 0xe0ffadffb2de83e0 0xfff67ff9cffc1f06 0x9ffecfff39ff83e0

def z61 : W := mkw 0x4020884220202630 0x08041108440404c6 0x0000080600000c60 0x00000100c000018c

def z62 : W := mkw 0x0200048806f41f04 0xe040009100de83e0 0x0a0000000ffc1f06 0x0140000001ff83e0

def z63 : W := mkw 0xa0023010d80a808a 0x140046021b015011 0x00067001c0000000 0x0000ce0038000000

def z64 : W := mkw 0x008c018501810841 0x40118030a0302108 0x27880b8603810c64 0x04f10170c070218c

def z65 : W := mkw 0x0571ea72b0000000 0x00ae3d4e56000000 0x8071f07830000000 0x500e3e0f06000000

def z66 : W := mkw 0x43708eea26f43f34 0xe86e11dd44de87e6 0xfff18ff83ffcff1e 0xdffe31ff07ff9fe3

def z67 : W := mkw 0x05fffb77bb5bc007 0x00bfff6ef76b7800 0xf7ffffffff9c0001 0xfefffffffff38000

def z68 : W := mkw 0xa08e259ddd8719cb 0xf411c4b3bbb0e339 0x778e0fffff831fff 0xaef1c1fffff063ff

def z69 : W := mkw 0x01de00000b530007 0x003bc000016a6000 0xfbfe00000fff0006 0x3f7fc00001ffe000

def z70 : W := mkw 0x85ffeb77f90300c3 0x10bffd6eff206018 0xf5fffffff00300e1 0xfebffffffe00601c

def z71 : W := mkw 0x02200ee804a41f00 0xe04401dd009483e0 0x77800ff80f801f06 0x8ef001ff01f003e0

def z72 : W := mkw 0x03df54880fffdf07 0xe07bea9101fffbe0 0xfbfff0000fffff06 0x7f7ffe0001ffffe0

def z73 : W := mkw 0x0000000000000000 0x0000000000000000 0x3008080600031ce7 0xa6010100c000639c

def z74 : W := mkw 0xc0ae8dc76da33ef3 0xd815d1b8edb467de 0xffef8fc7ffe3ffff 0xfffdf1f8fffc7fff

def z75 : W := mkw 0x80000585448018c0 0xd00000b0a8900318 0x04000f87c0001ce1 0x808001f0f800039c

def z76 : W := mkw 0x00021000080a8002 0x0000420001015000 0xd81670000c1e8002 0x7b02ce000183d000

def z77 : W := mkw 0x808e15854d8b98c3 0xd011c2b0a9b17318 0xff9e7f87cf9f9ce7 0xfff3cff0f9f3f39c

def z78 : W := mkw 0x0020884220000000 0x0004110844000000 0xb86988463002939b 0xf70d3108c6005273

def z79 : W := mkw 0x0350022802540104 0x206a0045004a8020 0x00100038001c0000 0x0002000700038000

def z80 : W := mkw 0x80ae8dc76d8318c3 0xd015d1b8edb06318 0xf7ef8fc7ff831ce7 0xfefdf1f8fff0639c

def z81 : W := mkw 0x035006a806d41904 0xe06a00d500da8320 0x77900fb80f9c1c06 0x8ef201f701f38380

def z82 : W := mkw 0x000214080c0e9102 0xa00042810181d220 0xd81674780c1e9302 0xfb02ce8f0183d260

def z83 : W := mkw 0x008f5000090bc003 0x0011ea0001217800 0xb86ff0000063e006 0x770dfe00000c7c00

def z84 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0xfff80ffe0fff1fe7 0xbfff01ffc1ffe3fc

def z85 : W := mkw 0x01dd400003514005 0x003ba800006a2800 0x23e9800003e16004 0x047d3000007c2c00

def z86 : W := mkw 0xa48ff51ffc0e918a 0xb491fea3ff81d231 0xd81ff47ffc1e939b 0xfb03fe8fff83d273

def z87 : W := mkw 0x008c010500000000 0x00118020a0000000 0x45860781c0000000 0x08b0c0f038000000

def z88 : W := mkw 0x45fdcb6720202630 0x08bfb96ce40404c6 0xbde98bc63063ffff 0xf7bd3178c60c7fff

def z89 : W := mkw 0x02200ee804a41f00 0xe04401dd009483e0 0xdc100ff80c1c1f02 0x9b8201ff018383e0

def z90 : W := mkw 0x800204804d8318c3 0xd000409009b06318 0x020000000f800000 0x0040000001f00000

def z91 : W := mkw 0x4020884220202630 0x08041108440404c6 0x2069880600616c64 0x040d3100c00c2d8c

def z92 : W := mkw 0x4420ab77b0202630 0x0884156ef60404c6 0xbc698ffff063ffff 0xf78d31fffe0c7fff

def z93 : W := mkw 0xa00214084c0e918a 0xb40042810981d231 0x080000000c1e939a 0x010000000183d273

def z94 : W := mkw 0x015150000258c004 0x002a2a00004b1800 0xfbf1f0000ffce006 0x5f7e3e0001ff9c00

def z95 : W := mkw 0x0000000000000000 0x0000000000000000 0x080000000002939a 0x0100000000005273

def z96 : W := mkw 0x01700a6000000000 0x002e014c00000000 0xf5f00ff800000000 0x9ebe01ff00000000

def z97 : W := mkw 0x0420ab77b0000000 0x0084156ef6000000 0xb4698ffff0000001 0xf68d31fffe000000

def z98 : W := mkw 0x0771ea7ab2740704 0x20ee3d4f564e80e0 0x8871f078307c0300 0x510e3e0f060f8060

def z99 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0xfff00ff83ffe9f9f 0xfffe01ff07ffd3f3

def z100 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0xfdfffffff002939b 0xffbffffffe005273

def z101 : W := mkw 0x6020b85ab02ca738 0x2c04170b560594e7 0xb879f87e307fffff 0xf70f3f0fc60fffff

def z102 : W := mkw 0x0000000003514005 0x00000000006a2800 0x0200000003e16004 0x00400000007c2c00

def z103 : W := mkw 0x0000201090000000 0x0000040212000000 0x00000479f0000001 0x8000008f3e000000

def z104 : W := mkw 0x85fdeff7f48018c0 0xd0bfbdfefe900318 0xf5fffffff0001ce1 0xfebffffffe00039c

def z105 : W := mkw 0x07fdefffb6d41904 0xe0ffbdfff6da8320 0xf7ffffffff9c0001 0xfefffffffff38000

def z106 : W := mkw 0xa0023010d80a808a 0x140046021b015011 0x00067001f0028099 0x6000ce003e005013

def z107 : W := mkw 0xc00204804da33ef3 0xd800409009b467de 0x0a0000000fe3fffe 0x0140000001fc7fff

def z108 : W := mkw 0x83ff5fed4fffdfc7 0xf07febfda9fffbf8 0xffffffffcfffffe7 0xfffffffff9fffffc

def z109 : W := mkw 0x02200ae000a00e00 0x4044015c001401c0 0x04000b8000000c00 0x0080017000000180

def z110 : W := mkw 0xa08f7010d90bc08b 0x1411ee021b217811 0x000ff001f003e099 0x6001fe003e007c13

def z111 : W := mkw 0x8002000048020082 0x1000400009004010 0x00060001c0020081 0x2000c00038004010

def z112 : W := mkw 0xe5ffff7ffc2eb7ba 0xbcbfffefff85d6f7 0xfdfffffffc7fffff 0xffbfffffff8fffff

def z113 : W := mkw 0x015350000b5bc007 0x002a6a00016b7800 0x8a71f0000fffe006 0x514e3e0001fffc00

def z114 : W := mkw 0x0000000000000000 0x0000000000000000 0x50060401c0000001 0xaa00c08038000000

def z115 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0x678e0f87cf810c64 0x0cf1c1f0f9f0218c

def z116 : W := mkw 0x01dd400000000000 0x003ba80000000000 0x21e9800000000000 0x043d300000000000

def z117 : W := mkw 0x008e018509830843 0x4011c030a1306108 0x778e0b860f830c66 0x2ef1c170c1f0618c

def z118 : W := mkw 0x0000048004801800 0xc000009000900300 0x478007800f800000 0x08f000f001f00000

def z119 : W := mkw 0x0000008001810841 0x4000001000302108 0x0200000003810c64 0x004000000070218c

def z120 : W := mkw 0xa08e158d4d8f99cb 0xf411c2b1a9b1f339 0x7f8e0f87cf9f9fff 0xaff1c1f0f9f3f3ff

def z121 : W := mkw 0x4020884220202630 0x08041108440404c6 0x886180403060e318 0x510c3008060c1c63

def z122 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0x47860781cf800000 0x08f0c0f039f00000

def z123 : W := mkw 0x808e0105490300c3 0x1011c020a9206018 0x00060001c0000000 0x0000c00038000000

def z124 : W := mkw 0x83fe0fed4ff71fc7 0xf07fc1fda9fee3f8 0xfffe0fffcfff1fe7 0xbfffc1fff9ffe3fc

def z125 : W := mkw 0xa35236b8dede998e 0xf46a46d71bdbd331 0x479677b9cf9c0000 0x08f2cef739f38000

def z126 : W := mkw 0x020006a804841900 0xe04000d500908320 0x040007b800000000 0x008000f700000000

def z127 : W := mkw 0xa0023010d80a808a 0x140046021b015011 0xd8167001fc1e809b 0x7b02ce003f83d013

def z128 : W := mkw 0x4020884220202630 0x08041108440404c6 0x080008463063ffff 0x81000108c60c7fff

def z129 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0x47860f87cf801ce1 0x88f0c1f0f9f0039c

def z130 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0xfbfff8060ffffce7 0xff7fff00c1ffff9c

def z131 : W := mkw 0x05dd633590000000 0x00bbac66b2000000 0xd59677f9f0000001 0xfab2ceff3e000000

def z132 : W := mkw 0x4000800220002030 0x0800100044000406 0x00000006300000f9 0x00000000c600001f

def z133 : W := mkw 0x808f55854d8bd8c3 0xd011eab0a9b17b18 0x778fff87cf83fce7 0xeef1fff0f9f07f9c

def z134 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0x807ff07ff0000001 0x700ffe0ffe000000

def z135 : W := mkw 0x04adeb77b0000000 0x0095bd6ef6000000 0x040ffffff0000001 0xe081fffffe000000

def z136 : W := mkw 0x41fdc84223716635 0x083fb908446e2cc6 0xbbe9884633e3ffff 0xf77d3108c67c7fff

def z137 : W := mkw 0x45fdcb6720202630 0x08bfb96ce40404c6 0x25e98b8600616c64 0x04bd3170c00c2d8c

def z138 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0x778e0f87cf800001 0xaef1c1f0f9f00000

def z139 : W := mkw 0x000210000b5bc007 0x00004200016b7800 0x020000000f9c0000 0x0040000001f38000

def z140 : W := mkw 0xc08e85876d8338f3 0xd811d0b0edb0671e 0x778f8f87ff83fcff 0xeef1f1f0fff07f9f

def z141 : W := mkw 0x05fdcb6720000000 0x00bfb96ce4000000 0x25e98b8600000000 0x04bd3170c0000000

def z142 : W := mkw 0x0000000000000000 0x0000000000000000 0x2008080600010c64 0x04010100c000218c

def z143 : W := mkw 0xa08e359ddd8f99cb 0xf411c6b3bbb1f339 0x779e7fbfcf9f1ce7 0xaef3cff7f9f3e39c

def z144 : W := mkw 0x02200ee804a41f00 0xe04401dd009483e0 0x04000ff800001f00 0x808001ff000003e0

def z145 : W := mkw 0x01dd400003514005 0x003ba800006a2800 0xf3fff00003e16004 0x7e7ffe00007c2c00

def z146 : W := mkw 0x008f5000090bc003 0x0011ea0001217800 0x000ff0000003e000 0x6001fe0000007c00

def z147 : W := mkw 0x0400233590000000 0x00800466b2000000 0x040007b9c0000000 0x008000f738000000

def z148 : W := mkw 0x47fdefffb6f43f34 0xe8ffbdfff6de87e6 0xffffffffffffffff 0xffffffffffffffff

def z149 : W := mkw 0x85ffcfe76d8318c3 0xd0bff9fcedb06318 0x77ef8f87cf831ce7 0xaefdf1f0f9f0639c

def z150 : W := mkw 0xa0023018d80e818a 0x340046031b01d031 0x88167079f01e8399 0x7102ce0f3e03d073

def z151 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0xcff007f80ffc0300 0x19fe00ff01ff8060

def z152 : W := mkw 0xa08e3115d90b80cb 0x1411c622bb217019 0x000e7007f00380f9 0x6001ce00fe00701f

def z153 : W := mkw 0x0000000000000000 0x0000000000000000 0x000980000003e000 0x6001300000007c00

def z154 : W := mkw 0x008e1000090b8003 0x0011c20001217000 0xfb9e70000f9f8006 0x7f73ce0001f3f000

def z155 : W := mkw 0x4020884220202630 0x08041108440404c6 0xb069884630001ff9 0xf60d3108c60003ff

def z156 : W := mkw 0x4000000000202630 0x08000000000404c6 0x080000000060e318 0x01000000000c1c63

def z157 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0x40167479fc1c1399 0x8802ce8f3f838273

def z158 : W := mkw 0x43708ae222f02e34 0x486e115c445e05c6 0x27e98b8603e16c64 0x04fd3170c07c2d8c

def z159 : W := mkw 0x03700ae002f00e04 0x406e015c005e01c0 0x27e00b8003e00c04 0x04fc0170007c0180

def z160 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0x739e70000f9f0006 0x2e73ce0001f3e000

def z161 : W := mkw 0x45fdeb77b0202630 0x08bfbd6ef60404c6 0xfdfffffff060e319 0xffbffffffe0c1c63

def z162 : W := mkw 0x05dd633590000000 0x00bbac66b2000000 0x759e7fbfc0000001 0xaeb3cff7f8000000

def z163 : W := mkw 0x00021000080a8002 0x0000420001015000 0x401670000c1c0000 0x0802ce0001838000

def z164 : W := mkw 0x05fdeb77b0200600 0x00bfbd6ef60400c0 0xfdfffffff0601f07 0xffbffffffe0c03e0

def z165 : W := mkw 0x0150022000000000 0x002a004400000000 0x459007b800000000 0x08b200f700000000

def z166 : W := mkw 0x0020884220000000 0x0004110844000000 0xb069884630031ce7 0xf60d3108c600639c

def z167 : W := mkw 0x000210000b5bc007 0x00004200016b7800 0x0a0000000fffe006 0x0140000001fffc00

def z168 : W := mkw 0xc3fe8fef6ff73ff7 0xf87fd1fdedfee7fe 0xffff8fffffffffff 0xfffff1ffffffffff

def z169 : W := mkw 0x015150000258c004 0x002a2a00004b1800 0xb879f000007fe006 0x770f3e00000ffc00

def z170 : W := mkw 0x00021000090bc003 0x0000420001217800 0x000000000003e000 0x0000000000007c00

def z171 : W := mkw 0x01fc0b6500000000 0x003f816ca0000000 0xf5fe0fffc0000001 0xbebfc1fff8000000

def z172 : W := mkw 0x02200cc806f41f04 0xe044019900de83e0 0xba6008400ffc1f06 0x974c010801ff83e0

def z173 : W := mkw 0x008c018501810841 0x40118030a0302108 0x778e0f87c3810c65 0xaef1c1f0f870218c

def z174 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0xff8e0fc7ff839fff 0xfff1c1f8fff073ff

def z175 : W := mkw 0x4000000000202630 0x08000000000404c6 0xb86980000063fffe 0x770d3000000c7fff

def z176 : W := mkw 0x808e04804d8318c3 0xd011c09009b06318 0x738e00000f831ce6 0x2e71c00001f0639c

def z177 : W := mkw 0xa20214884efe9f8e 0xf440429109dfd3f1 0x0a0000000ffe9f9e 0x0140000001ffd3f3

def z178 : W := mkw 0xa5fffffffd8f99cb 0xf4bfffffffb1f339 0xffffffffff9f9fff 0xfffffffffff3f3ff

def z179 : W := mkw 0x43700ee806f43f34 0xe86e01dd00de87e6 0xfff00ff80ffffffe 0x9ffe01ff01ffffff

def z180 : W := mkw 0x03700a6802740704 0x206e014d004e80e0 0xfbf000780ffc0306 0x1f7e000f01ff8060

def z181 : W := mkw 0x81df45854fd358c7 0xd03be8b0a9fa6b18 0x77ef8f87cfe37ce7 0xaefdf1f0f9fc6f9c

def z182 : W := mkw 0x0000000000000000 0x0000000000000000 0x9800004000001302 0x9300000800000260

def z183 : W := mkw 0x05fd6b7590000000 0x00bfad6eb2000000 0xf5f67ff9c0000000 0x9ebecfff38000000

def z184 : W := mkw 0xc08e05854da33ef3 0xd811c0b0a9b467de 0x7f8e0f87cfe3ffff 0xaff1c1f0f9fc7fff

def z185 : W := mkw 0x03ff5ae00bfbce07 0x407feb5c017f79c0 0xfffffb800fffec06 0x7fffff7001fffd80

def z186 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0xc8167479fc1c8318 0x5902ce8f3f839063

def z187 : W := mkw 0xe022bc5afc2eb7ba 0xbc04578b5f85d6f7 0xd8167c7ffc1e9ffb 0xfb02cf8fff83d3ff

def z188 : W := mkw 0x81df55854fdbd8c7 0xd03beab0a9fb7b18 0x47967781cf9c0000 0x08f2cef039f38000

def z189 : W := mkw 0xe0023418dc2eb7ba 0xbc0046831b85d6f7 0xd8167479fc7fffff 0xfb02ce8f3f8fffff

def z190 : W := mkw 0x43ffdeea2fffff37 0xe87ffbdd45ffffe6 0xfffffffe3fffffff 0xffffffffc7ffffff

def z191 : W := mkw 0x4020884220202630 0x08041108440404c6 0x0000004030000318 0x0000000806000063

def z192 : W := mkw 0x83700fed46f41fc4 0xf06e01fda8de83f8 0xfff00fffcffc1fe7 0x9ffe01fff9ff83fc

def z193 : W := mkw 0x43708eea26f43f34 0xe86e11dd44de87e6 0xfff98ffe0ffd7f66 0x9fff31ffc1ffafec

def z194 : W := mkw 0x048ff117b90bc003 0x0091fe22f7217800 0x000ff007f003e001 0x6001fe00fe007c00

def z195 : W := mkw 0x008f5000090bc003 0x0011ea0001217800 0xd81ff0000c1fe002 0x7b03fe000183fc00

def z196 : W := mkw 0x03708eea26f41f04 0xe06e11dd44de83e0 0xfff98ffe3ffc1f07 0xffff31ffc7ff83e0

def z197 : W := mkw 0xe00214084c2eb7ba 0xbc0042810985d6f7 0x080000000c7ffffe 0x01000000018fffff

def z198 : W := mkw 0xa00214884d8f99cb 0xf400429109b1f339 0x0a0000000f9f9ffe 0x0140000001f3f3ff

def z199 : W := mkw 0x01df5000090bc003 0x003bea0001217800 0xf1fff0000003e000 0x7e3ffe0000007c00

def z200 : W := mkw 0x0020084000200600 0x00040108000400c0 0x8860004000600300 0x110c0008000c0060

def z201 : W := mkw 0x0000010500000000 0x00000020a0000000 0x04000f87c0000001 0x808001f0f8000000

def z202 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0x4b9670000fffe006 0x0972ce0001fffc00

def z203 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0xdb9670000f9e8002 0x7b72ce0001f3d000

def z204 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0x47900ff80f9c1f00 0x88f201ff01f383e0

def z205 : W := mkw 0x0000000000000000 0x0000000000000000 0xb069800000000000 0x760d300000000000

def z206 : W := mkw 0x048de117b0000000 0x0091bc22f6000000 0x000ff007f0000001 0x6001fe00fe000000

def z207 : W := mkw 0x0000000000000000 0x0000000000000000 0x2069800000616004 0x040d3000000c2c00

def z208 : W := mkw 0x03700ee804a41f00 0xe06e01dd009483e0 0xf5f00ff800001f00 0x9ebe01ff000003e0

def z209 : W := mkw 0x0020a852b0000000 0x0004150a56000000 0xf07ffc7ff0000001 0xfe0fff8ffe000000

def z210 : W := mkw 0x0150000002500004 0x002a0000004a0000 0x23e0000003e00004 0x047c0000007c0000

def z211 : W := mkw 0xa00214084c0e918a 0xb40042810981d231 0xd81670000c1e939a 0x7b02ce000183d273

def z212 : W := mkw 0x03700ae002f00e04 0x406e015c005e01c0 0xfff00b800ffc0c06 0x1ffe017001ff8180

def z213 : W := mkw 0x81df51054b5bc0c7 0x103bea20a96b7818 0xfbfff007cfffe0e7 0x7f7ffe00f9fffc1c

def z214 : W := mkw 0x0020884220000000 0x0004110844000000 0x0000084630000001 0x80000108c6000000

def z215 : W := mkw 0x0150000002500004 0x002a0000004a0000 0x439000000f9c0000 0x0872000001f38000

def z216 : W := mkw 0x03700a6802740704 0x206e014d004e80e0 0x88700078007c0300 0x110e000f000f8060

def z217 : W := mkw 0x05dd432500000000 0x00bba864a0000000 0x0580038000000000 0x00b0007000000000

def z218 : W := mkw 0x800204804d8318c3 0xd000409009b06318 0x020000000f831ce6 0x0040000001f0639c

def z219 : W := mkw 0x0000000000000000 0x0000000000000000 0xd81000000c1c0002 0x1b02000001838000

def z220 : W := mkw 0x020214880fffdf07 0xe040429101fffbe0 0x0a0000000fffff06 0x0140000001ffffe0

def z221 : W := mkw 0x44ade957b0202630 0x0895bd2af60404c6 0xb86ff847f063ffff 0xf70dff08fe0c7fff

def z222 : W := mkw 0x20003018900c8108 0x2400060312019021 0xd8167479f01c8319 0xfb02ce8f3e039063

def z223 : W := mkw 0x008c211590000000 0x00118422b2000000 0xf59e7ffff0000001 0xfeb3cffffe000000

def z224 : W := mkw 0x0571ea72b0000000 0x00ae3d4e56000000 0xd077f479f0000001 0xfa0efe8f3e000000

def z225 : W := mkw 0x035006a806d41904 0xe06a00d500da8320 0xfff007b80ffc0006 0x1ffe00f701ff8000

def z226 : W := mkw 0x808e0105490300c3 0x1011c020a9206018 0x300e0807c0031ce7 0xa601c100f800639c

def z227 : W := mkw 0x848fe117f90300c3 0x1091fc22ff206018 0x000ff007f00300e1 0x6001fe00fe00601c

def z228 : W := mkw 0x0571ca6220000000 0x00ae394c44000000 0x0061800000000000 0x000c300000000000

def z229 : W := mkw 0x01700e6804041100 0xa02e01cd00808220 0xfdf00ff80c1c1302 0x9fbe01ff01838260

def z230 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0x48167439cc1e939a 0x0902ce873983d273

def z231 : W := mkw 0x0000201090000000 0x0000040212000000 0x40167439c0000000 0x0802ce8738000000

def z232 : W := mkw 0xc1ffddc76ffbfef7 0xd83ffbb8edff7fde 0xffffffc7ffffffff 0xfffffff8ffffffff

def z233 : W := mkw 0x05fdcb6720000000 0x00bfb96ce4000000 0xf5fffb8600000000 0x7ebfff70c0000000

def z234 : W := mkw 0xa08e3418dd0f918b 0xb411c6831ba1f231 0xfb9e7479ff9f939f 0xff73ce8f3ff3f273

def z235 : W := mkw 0x20001008000c8108 0x2400020100019021 0x08000000001c8318 0x0100000000039063

def z236 : W := mkw 0x01dd400002500004 0x003ba800004a0000 0xfbfff0000ffc0006 0x7f7ffe0001ff8000

def z237 : W := mkw 0xa0023498dd8f99cb 0xf40046931bb1f339 0xda167479ff9f9fff 0xfb42ce8f3ff3f3ff

def z238 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0x27880b860f831ce6 0x04f10170c1f0639c

def z239 : W := mkw 0x008e04800d831803 0xc011c09001b06300 0x778e0f800f831c06 0xaef1c1f001f06380

def z240 : W := mkw 0x0571fa72b258c004 0x00ae3f4e564b1800 0x8871f078307ce000 0x510e3e0f060f9c00

def z241 : W := mkw 0x048d611590000000 0x0091ac22b2000000 0x00067001c0000000 0x0000ce0038000000

def z242 : W := mkw 0x03702ef896f41f04 0xe06e05df12de83e0 0xfff67ff9fffc1f07 0xfffecfff3fff83e0

def z243 : W := mkw 0x00200a6000000000 0x0004014c00000000 0x04000ff800000000 0x808001ff00000000

def z244 : W := mkw 0x03fd4ee806f41f04 0xe07fa9dd00de83e0 0xfffffff80ffc1f06 0xffffffff01ff83e0

def z245 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0x45967ffff0000001 0x88b2cffffe000000

def z246 : W := mkw 0x0000000000000000 0x0000000000000000 0x886180000060e000 0x510c3000000c1c00

def z247 : W := mkw 0x0000040804041100 0xa000008100808220 0xd81004783c1e939b 0xfb02008f0783d273

def z248 : W := mkw 0x808e05054d0310c3 0x9011c0a0a9a06218 0x500e0407cc0310e3 0xaa01c080f980621c

def z249 : W := mkw 0xa000259dd48419c8 0xf40004b3ba908339 0x04000ffff0001ff9 0x808001fffe0003ff

def z250 : W := mkw 0x0000048804841900 0xe000009100908320 0xff900ff80f9c1f06 0x9ff201ff01f383e0

def z251 : W := mkw 0x4170884222702634 0x082e1108444e04c6 0xfbf988463fffffff 0xff7f3108c7ffffff

def z252 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000080600001ce1 0x80000100c000039c

def z253 : W := mkw 0x01ff5a600b5bc007 0x003feb4c016b7800 0xfffffff80fffe006 0xffffffff01fffc00

def z254 : W := mkw 0x808e0185498308c3 0x5011c030a9306118 0x278e0b87c3830ce5 0x24f1c170f870619c

def z255 : W := mkw 0x84aeaff7fd8318c3 0xd095d5feffb06318 0x778e0fffff831ce7 0xaef1c1fffff0639c

def z256 : W := mkw 0x0151400002504004 0x002a2800004a0800 0x0061800000606000 0x000c3000000c0c00

def z257 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0xfbf670000ffc0006 0x1f7ece0001ff8000

def z258 : W := mkw 0x45fffb77bb7be637 0x08bfff6ef76f7cc6 0xffffffffffffffff 0xffffffffffffffff

def z259 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0xffef8f87cfe3fce7 0xfffdf1f0f9fc7f9c

def z260 : W := mkw 0xa0021000480a808a 0x1400420009015011 0x0000000000028098 0x0000000000005013

def z261 : W := mkw 0x40afd842292be633 0x0815fb0845257cc6 0xb86ff8463063ffff 0xf70dff08c60c7fff

def z262 : W := mkw 0xa0002418d4041188 0xb40004831a808231 0x98000479f002939b 0xf300008f3e005273

def z263 : W := mkw 0x0000000000000000 0x0000000000000000 0x3000080000001c06 0x8600010000000380

def z264 : W := mkw 0x00021000080a8002 0x0000420001015000 0x080000000c1e8002 0x010000000183d000

def z265 : W := mkw 0x81df55854fdbd8c7 0xd03beab0a9fb7b18 0x779e7f87cf9f1ce7 0xaef3cff0f9f3e39c

def z266 : W := mkw 0xa1df7418df5fd18f 0xb43bee831bebfa31 0xdb967479ff9e939b 0xfb72ce8f3ff3d273

def z267 : W := mkw 0x4000000000002030 0x0800000000000406 0x000000000003e0f8 0x0000000000007c1f

def z268 : W := mkw 0x4571ea72b0202630 0x08ae3d4e560404c6 0x8871f0783060e318 0x510e3e0f060c1c63

def z269 : W := mkw 0x05dd633590000000 0x00bbac66b2000000 0xf5fff7b9c0000000 0x7ebffef738000000

def z270 : W := mkw 0x20003018900c8108 0x2400060312019021 0x88107078301c8318 0x51020e0f06039063

def z271 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000004030001399 0x8000000806000273

def z272 : W := mkw 0x05fffb77b80a8002 0x00bfff6ef7015000 0xfdfffffffc1e8003 0xffbfffffff83d000

def z273 : W := mkw 0x01702a7090000000 0x002e054e12000000 0xf5f67ff9f0000001 0xfebecfff3e000000

def z274 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0x040e0f87c0031ce1 0xa081c1f0f800639c

def z275 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0x2fe00b800ffc1f06 0x05fc017001ff83e0

def z276 : W := mkw 0x800204004c021082 0x9000408009804210 0x40060401cc000000 0x0800c08039800000

def z277 : W := mkw 0xa1df7418dc0e918a 0xb43bee831b81d231 0xf9fff479fc1e939b 0xff3ffe8f3f83d273

def z278 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0x08067001fc1e939b 0x6100ce003f83d273

def z279 : W := mkw 0x035006a806d41904 0xe06a00d500da8320 0xdf9007f80f9c1302 0x9bf200ff01f38260

def z280 : W := mkw 0x00023010980a8002 0x0000460213015000 0xd8167479fc1e8003 0xfb02ce8f3f83d000

def z281 : W := mkw 0x808e05054c021082 0x9011c0a0a9804210 0x758e0f87cc021083 0xaeb1c1f0f9804210

def z282 : W := mkw 0x008c000000000000 0x0011800000000000 0x718e000000000000 0x2e31c00000000000

def z283 : W := mkw 0x05ffeb77b9030003 0x00bffd6ef7206000 0xf7ffffffff830007 0xfefffffffff06000

def z284 : W := mkw 0xa3fe3ffddfff9fcf 0xf47fc7ffbbfff3f9 0xfffe7fffffff9fff 0xffffcffffffff3ff

def z285 : W := mkw 0xa00214084c0e918a 0xb40042810981d231 0x000000000c1c0000 0x0000000001838000

def z286 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0xc5f7f7f9f0000000 0x58befeff3e000000

def z287 : W := mkw 0x01700a6002500004 0x002e014c004a0000 0xfff00ff80ffc0006 0x9ffe01ff01ff8000

def z288 : W := mkw 0x4000800220002030 0x0800100044000406 0x000980063003e0f9 0x60013000c6007c1f

def z289 : W := mkw 0xa5df773ddc0e918a 0xb4bbeee7bb81d231 0xdd9677f9fc1e939b 0xfbb2ceff3f83d273

def z290 : W := mkw 0x01df5000080a8002 0x003bea0001015000 0xf9fff0000c1e8002 0x7f3ffe000183d000

def z291 : W := mkw 0xc08e8107690320f3 0x1811d020ed20641e 0x000f8007f003e0f9 0x6001f000fe007c1f

def z292 : W := mkw 0x448de117b0002030 0x0891bc22f6000406 0x000ff007f003e0f9 0x6001fe00fe007c1f

def z293 : W := mkw 0x83fe0fed4ff71fc7 0xf07fc1fda9fee3f8 0xfff60ff9cffc1f06 0x9ffec1ff39ff83e0

def z294 : W := mkw 0x4000000000202630 0x08000000000404c6 0x080000000063fffe 0x01000000000c7fff

def z295 : W := mkw 0x008e000009030003 0x0011c00001206000 0x000e000000030000 0x2001c00000006000

def z296 : W := mkw 0xa0002418d4041188 0xb40004831a808231 0x00000439c0000000 0x0000008738000000

def z297 : W := mkw 0x05fffa72bb5bc007 0x00bfff4e576b7800 0xfbfff0783fffe006 0x7f7ffe0f07fffc00

def z298 : W := mkw 0xe1fffc5aff7ff7bf 0xbc3fff8b5feffef7 0xfbfffc7fffffffff 0xff7fff8fffffffff

def z299 : W := mkw 0x01dd418503d14845 0x403ba830a07a2908 0x27e98b8603e16c64 0x04fd3170c07c2d8c

def z300 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0x778e0781cf830006 0x2ef1c0f039f06000

def z301 : W := mkw 0xa1df759ddfdfd9cf 0xf43beeb3bbfbfb39 0xffffffffffffffff 0xffffffffffffffff

def z302 : W := mkw 0x0020884220000000 0x0004110844000000 0xb069884630000001 0xf60d3108c6000000

def z303 : W := mkw 0x81df55854fdbd8c7 0xd03beab0a9fb7b18 0xfffff781cfffe006 0x7ffffef039fffc00

def z304 : W := mkw 0x03df56a80fdfd907 0xe07bead501fbfb20 0x479677b80f9c0000 0x08f2cef701f38000

def z305 : W := mkw 0x05fdcbe721810841 0x40bfb97ce4302108 0x27e98b8603810c64 0x04fd3170c070218c

def z306 : W := mkw 0xa08f7418dd0fd18b 0xb411ee831ba1fa31 0xd81ff479fc1ff39b 0xfb03fe8f3f83fe73

def z307 : W := mkw 0x20003018900c8108 0x2400060312019021 0x98107078301e939b 0xf3020e0f0603d273

def z308 : W := mkw 0x05dde117b0000000 0x00bbbc22f6000000 0xf1fff007f0000001 0x7e3ffe00fe000000

def z309 : W := mkw 0x81df45854d8318c3 0xd03be8b0a9b06318 0xf7ffff87cf831ce7 0xfefffff0f9f0639c

def z310 : W := mkw 0x800205854c8218c2 0xd00040b0a9904318 0x54060f87cc021ce3 0xaa80c1f0f980439c

def z311 : W := mkw 0x4000800220202630 0x08001000440404c6 0x080980063063ffff 0x61013000c60c7fff

def z312 : W := mkw 0x80022410dc021082 0x900044821b804210 0xd0167479fc021083 0xfa02ce8f3f804210

def z313 : W := mkw 0x03700ae802f40f04 0x606e015d005e81e0 0xaff00bf803fc0f04 0x15fe017f007f81e0

def z314 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z315 : W := mkw 0x000150000008c000 0x00002a0000011800 0x0001f0000000e000 0x40003e0000001c00

def z316 : W := mkw 0x07dd67bd96d41904 0xe0fbacf7b2da8320 0x479677b9cf9c0000 0x08f2cef739f38000

def z317 : W := mkw 0x05fdef7fb4041100 0xa0bfbdeff6808220 0xfdfffffffc1c1303 0xffbfffffff838260

def z318 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0xfbfff0403ffff39f 0xff7ffe0807fffe73

def z319 : W := mkw 0xe002b012f80aa0ba 0x1c0056025f015417 0x000ff007f003e0f9 0x6001fe00fe007c1f

def z320 : W := mkw 0xa08e359ddd8f99cb 0xf411c6b3bbb1f339 0x479677b9cf9c0000 0x08f2cef739f38000

def z321 : W := mkw 0x03fd4ae003f14e05 0x407fa95c007e29c0 0x27e98b8003e16c04 0x04fd3170007c2d80

def z322 : W := mkw 0x0170084002700604 0x002e0108004e00c0 0xfbf008400ffc1f06 0x9f7e010801ff83e0

def z323 : W := mkw 0x0000000000000000 0x0000000000000000 0xd010047800000000 0x9a02008f00000000

def z324 : W := mkw 0x4020884220202630 0x08041108440404c6 0x206988063063ecfd 0x640d3100c60c7d9f

def z325 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0x40167439fc1e8099 0x6802ce873f83d013

def z326 : W := mkw 0x83de07ad4fd719c7 0xf07bc0f5a9fae338 0x779e0fbfcf9f1ce7 0xaef3c1f7f9f3e39c

def z327 : W := mkw 0x03700a6802740704 0x206e014d004e80e0 0xfdf00ff8007c0300 0x9fbe01ff000f8060

def z328 : W := mkw 0x0571eb77b0000000 0x00ae3d6ef6000000 0x8471fffff0000001 0xd08e3ffffe000000

def z329 : W := mkw 0x048de117b0000000 0x0091bc22f6000000 0x758fff87f0000001 0xeeb1fff0fe000000

def z330 : W := mkw 0x0000048004801800 0xc000009000900300 0x77880f860f831ce7 0xaef101f0c1f0639c

def z331 : W := mkw 0x808e058d4d8719c3 0xf011c0b1a9b0e338 0xff9e0fffcf9f1fe7 0xbff3c1fff9f3e3fc

def z332 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0xcbf7f0000ffce000 0x597efe0001ff9c00

def z333 : W := mkw 0x45fdeb77b0002030 0x08bfbd6ef6000406 0xf5fffffff003e0f9 0xfebffffffe007c1f

def z334 : W := mkw 0x03700ee806d41904 0xe06e01dd00da8320 0xf7f00ff80f9c0000 0x9efe01ff01f38000

def z335 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0xf5fffffff0031ce7 0xfebffffffe00639c

def z336 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0xfff98ff80fffff06 0xffff31ff01ffffe0

def z337 : W := mkw 0x05df73359b5bc007 0x00bbee66b36b7800 0xfffff7b9cfffe006 0x7ffffef739fffc00

def z338 : W := mkw 0x0000201090000000 0x0000040212000000 0x8010707830000000 0x50020e0f06000000

def z339 : W := mkw 0x0000000000000000 0x0000000000000000 0xd016700000000000 0x7a02ce0000000000

def z340 : W := mkw 0x008c018501810841 0x40118030a0302108 0x0780038003800000 0x00f0007000700000

def z341 : W := mkw 0x000210000b5bc007 0x00004200016b7800 0xba6980000fffe006 0x774d300001fffc00

def z342 : W := mkw 0x83720ee84ef61f86 0xf06e41dd09dec3f0 0xfff60ff9cffe1f87 0xbffec1ff39ffc3f0

def z343 : W := mkw 0x05fffb77b90bc003 0x00bfff6ef7217800 0xf5fffffff003e001 0xfebffffffe007c00

def z344 : W := mkw 0x0000000800040100 0x2000000100008020 0x88100078001c0300 0x1102000f00038060

def z345 : W := mkw 0x25fdfb7fb00c8108 0x24bfbf6ff6019021 0xfdfffffff01c8319 0xffbffffffe039063

def z346 : W := mkw 0x0002000009030003 0x0000400001206000 0x020000000f830006 0x0040000001f06000

def z347 : W := mkw 0xa420af7ff4041188 0xb48415effe808231 0x04000ffff0001399 0x808001fffe000273

def z348 : W := mkw 0x05fdeb77b2500004 0x00bfbd6ef64a0000 0xfffffffffffc0007 0xffffffffffff8000

def z349 : W := mkw 0xa7fffffffefe9f8e 0xf4ffffffffdfd3f1 0xfffffffffffe9f9f 0xffffffffffffd3f3

def z350 : W := mkw 0x82ae0fed4da71fc3 0xf055c1fda9b4e3f8 0x778e0fffcf831fe7 0xaef1c1fff9f063fc

def z351 : W := mkw 0x4571ea72b0202630 0x08ae3d4e560404c6 0xb879f87e3063ffff 0xf70f3f0fc60c7fff

def z352 : W := mkw 0xa573fe7afc0e918a 0xb4ae7fcf5f81d231 0xd877f479fc1e939b 0xfb0efe8f3f83d273

def z353 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0x63fff0000ffd6004 0x0c7ffe0001ffac00

def z354 : W := mkw 0x008c010500000000 0x00118020a0000000 0x25880b8600000000 0x04b10170c0000000

def z355 : W := mkw 0x4020884220202630 0x08041108440404c6 0x286988060063fffe 0x050d3100c00c7fff

def z356 : W := mkw 0x80000585448018c0 0xd00000b0a8900318 0x04000781c0000000 0x008000f038000000

def z357 : W := mkw 0x40229842282aa632 0x08045308450554c6 0xf87ff8463c7fffff 0xff0fff08c78fffff

def z358 : W := mkw 0xa35236b8dede998e 0xf46a46d71bdbd331 0xdf9677f9ff9e939b 0xfbf2ceff3ff3d273

def z359 : W := mkw 0x00021000080a8002 0x0000420001015000 0xf87ff0000c7fe006 0x7f0ffe00018ffc00

def z360 : W := mkw 0x800204004c021082 0x9000408009804210 0x700e0c07cc031ce7 0xae01c180f980639c

def z361 : W := mkw 0x03715a68027cc704 0x206e2b4d004f98e0 0x8871f078007ce300 0x510e3e0f000f9c60

def z362 : W := mkw 0x80ae0dc54da31ec3 0xd015c1b8a9b463d8 0xffee0fc7cfe31fe7 0xbffdc1f8f9fc63fc

def z363 : W := mkw 0x0000040004001000 0x8000008000800200 0x500004000c001002 0x8a00008001800200

def z364 : W := mkw 0xc0228c426c2236b2 0x980451884d8446d6 0xf86f8c47fc63ffff 0xff0df188ff8c7fff

def z365 : W := mkw 0x015210000a5a8006 0x002a4200014b5000 0xfbf670000ffe8006 0x7f7ece0001ffd000

def z366 : W := mkw 0x4420ab77b0202630 0x0884156ef60404c6 0x04000ffff0001ff9 0x808001fffe0003ff

def z367 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0x65ffffbfc0000000 0x0cbffff7f8000000

def z368 : W := mkw 0xa5ffff7fff5fd18f 0xb4bfffefffebfa31 0xfffffffffffff39f 0xfffffffffffffe73

def z369 : W := mkw 0x400210000b7be637 0x08004200016f7cc6 0x0a0000000ffffffe 0x0140000001ffffff

def z370 : W := mkw 0x01df400009030003 0x003be80001206000 0xf3fff0000f830006 0x7e7ffe0001f06000

def z371 : W := mkw 0xa0002418d4041188 0xb40004831a808231 0xd0167479f0001399 0xfa02ce8f3e000273

def z372 : W := mkw 0x0420ab77b0000000 0x0084156ef6000000 0xd4167ffff0000001 0xfa82cffffe000000

def z373 : W := mkw 0x0020084000000000 0x0004010800000000 0xb060084000000000 0x960c010800000000

def z374 : W := mkw 0x42208eea24a43f30 0xe84411dd449487e6 0x04000ffe30001ff9 0x808001ffc60003ff

def z375 : W := mkw 0xa08e351ddc0e918a 0xb411c6a3bb81d231 0xfd9e7ffffc1e939b 0xffb3cfffff83d273

def z376 : W := mkw 0x04208b6720000000 0x0084116ce4000000 0x04000b8600000000 0x00800170c0000000

def z377 : W := mkw 0xa002359ddc8e99ca 0xf40046b3bb91d339 0xdc167ffffc1e9ffb 0xfb82cfffff83d3ff

def z378 : W := mkw 0x0000000000000000 0x0000000000000000 0x00080006000300e1 0x20010000c000601c

def z379 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0x23eff00003e3e004 0x647dfe00007c7c00

def z380 : W := mkw 0x0020884220000000 0x0004110844000000 0x2069880600000000 0x040d3100c0000000

def z381 : W := mkw 0x808c0585458118c1 0xd01180b0a8b02318 0x27880f87c3811ce5 0x84f101f0f870239c

def z382 : W := mkw 0x008e010509030003 0x0011c020a1206000 0x778e0f87cf830007 0xaef1c1f0f9f06000

def z383 : W := mkw 0x0000000000000000 0x0000000000000000 0x3008000000030006 0x2601000000006000

def z384 : W := mkw 0x0150048006d01804 0xc02a009000da0300 0xfff00f800ffc1c06 0x9ffe01f001ff8380

def z385 : W := mkw 0x0620afffb4a41f00 0xe0c415fff69483e0 0x04000ffff0001f01 0x808001fffe0003e0

def z386 : W := mkw 0x0000040804041100 0xa000008100808220 0x080000000c1c1302 0x0100000001838260

def z387 : W := mkw 0x85df67b5dd8318c3 0xd0bbecf6bbb06318 0x479677b9cf800000 0x08f2cef739f00000

def z388 : W := mkw 0x4020884220202630 0x08041108440404c6 0x3069880600637ce7 0xa60d3100c00c6f9c

def z389 : W := mkw 0xe372befafefebfbe 0xfc6e57df5fdfd7f7 0xffffffffffffffff 0xffffffffffffffff

def z390 : W := mkw 0x01ffd8422b5bc007 0x003ffb08456b7800 0xfbfff8463fffe007 0xff7fff08c7fffc00

def z391 : W := mkw 0x0200048804a41f00 0xe0400091009483e0 0x0000000000001f00 0x00000000000003e0

def z392 : W := mkw 0x03ff5ee80fffdf07 0xe07febdd01fffbe0 0xfff67ff80ffc1f06 0x9ffecfff01ff83e0

def z393 : W := mkw 0x0020084000200600 0x00040108000400c0 0xb868084600631fe7 0xb70d0108c00c63fc

def z394 : W := mkw 0x8420aff7f48018c0 0xd08415fefe900318 0x04000ffff0001ce1 0x808001fffe00039c

def z395 : W := mkw 0xa1523418de5e918e 0xb42a46831bcbd231 0xfbf67479fffe939f 0xff7ece8f3fffd273

def z396 : W := mkw 0x80000585448018c0 0xd00000b0a8900318 0x77800f87cf801ce7 0x8ef001f0f9f0039c

def z397 : W := mkw 0xa5fdef7ff4041188 0xb4bfbdeffe808231 0xf5fffffff0001399 0xfebffffffe000273

def z398 : W := mkw 0x0000000000000000 0x0000000000000000 0x8800004030008318 0x5100000806001063

def z399 : W := mkw 0x0000000002500004 0x00000000004a0000 0x0a0000000ffc0006 0x0140000001ff8000

def z400 : W := mkw 0x0570ab77b0000000 0x00ae156ef6000000 0xf5f00ffff0000001 0x9ebe01fffe000000

def z401 : W := mkw 0xa0022418dc06118a 0xb40044831b80c231 0x50060479fc02139b 0xaa00c08f3f804273

def z402 : W := mkw 0x43708a6a22742734 0x286e114d444e84e6 0x88718078307ce318 0x510e300f060f9c63

def z403 : W := mkw 0xc0228cc26da33ef3 0xd80451984db467de 0xba6988463fe3ffff 0xf74d3108c7fc7fff

def z404 : W := mkw 0x03fe0ee80ff71f07 0xe07fc1dd01fee3e0 0xfffe0ff80fff1f06 0xbfffc1ff01ffe3e0

def z405 : W := mkw 0x05fdcb6720000000 0x00bfb96ce4000000 0xf5f98ffe00000000 0x9ebf31ffc0000000

def z406 : W := mkw 0xa3721ee84efe9f8e 0xf46e43dd09dfd3f1 0xfff00ff80ffe9f9e 0x9ffe01ff01ffd3f3

def z407 : W := mkw 0x015350000a5ac006 0x002a6a00014b5800 0xd877f0000c7ee002 0x7b0efe00018fdc00

def z408 : W := mkw 0x01df51850bdbc847 0x403bea30a17b7908 0xfffffb860fffec66 0x7fffff70c1fffd8c

def z409 : W := mkw 0x07ffffffbfffdf07 0xe0fffffff7fffbe0 0xffffffffffffff07 0xffffffffffffffe0

def z410 : W := mkw 0x0020884220000000 0x0004110844000000 0xb86988463063e007 0xf70d3108c60c7c00

def z411 : W := mkw 0x0000241894041100 0xa000048312808220 0xd8167479fc1c1303 0xfb02ce8f3f838260

def z412 : W := mkw 0xa2023498defe9f8e 0xf44046931bdfd3f1 0xda167479fffe9f9f 0xfb42ce8f3fffd3f3

def z413 : W := mkw 0x008c058505811841 0xc01180b0a0b02308 0x77880f860f811c66 0x8ef101f0c1f0238c

def z414 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0xd0167479fc1c0001 0xfa02ce8f3f838000

def z415 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0x881070783c1e939a 0x51020e0f0783d273

def z416 : W := mkw 0x808e2595dd8318c3 0xd011c4b2bbb06318 0xf79e7fffff831ce7 0xfef3cffffff0639c

def z417 : W := mkw 0x85ffeff7fd8318c3 0xd0bffdfeffb06318 0xf7ffffffff800001 0xfefffffffff00000

def z418 : W := mkw 0x05fdcb6720000000 0x00bfb96ce4000000 0x75ef8f87c0000001 0xaebdf1f0f8000000

def z419 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0x47860781cf831ce6 0x08f0c0f039f0639c

def z420 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0x67f00fb80ffc0c04 0x0cfe01f701ff8180

def z421 : W := mkw 0xa0002418d4041188 0xb40004831a808231 0xd8100479fc1c139b 0x9b02008f3f838273

def z422 : W := mkw 0x2000201890040108 0x2400040312008021 0x0000007830000318 0x0000000f06000063

def z423 : W := mkw 0x03fd4ee807f55f05 0xe07fa9dd00feabe0 0xfff98ff80ffd7f06 0x9fff31ff01ffafe0

def z424 : W := mkw 0x008e10000b5bc007 0x0011c200016b7800 0x7b8e00000fffe006 0x2f71c00001fffc00

def z425 : W := mkw 0x4020884220202630 0x08041108440404c6 0x000988463003fff9 0xe0013108c6007fff

def z426 : W := mkw 0x01fd4a6000000000 0x003fa94c00000000 0xf5fffff800000000 0xfebfffff00000000

def z427 : W := mkw 0x00021000080a8002 0x0000420001015000 0xd81670403c1e939b 0xfb02ce080783d273

def z428 : W := mkw 0x80000480448018c0 0xd000009008900318 0x0000000000001ce0 0x000000000000039c

def z429 : W := mkw 0x0000000000000000 0x0000000000000000 0x080000000063e006 0x01000000000c7c00

def z430 : W := mkw 0x800204804d8318c3 0xd000409009b06318 0x77800f800f831ce6 0x8ef001f001f0639c

def z431 : W := mkw 0x035002a002d00804 0x406a0054005a0100 0x0780038003800000 0x00f0007000700000

def z432 : W := mkw 0x800204004c021082 0x9000408009804210 0xd8060441fc02939b 0xfb00c0883f805273

def z433 : W := mkw 0x4000000000202630 0x08000000000404c6 0x0000000000001ff8 0x00000000000003ff

def z434 : W := mkw 0x008e000009030003 0x0011c00001206000 0x438600000f800000 0x0870c00001f00000

def z435 : W := mkw 0x05dde337b0000000 0x00bbbc66f6000000 0x459ff7bff0000001 0x68b3fef7fe000000

def z436 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0x50167439cc1e1083 0xaa02ce873983c210

def z437 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0x57860781cf821083 0xaaf0c0f039f04210

def z438 : W := mkw 0xa0023418df5fd18f 0xb40046831bebfa31 0xda167479fffff39f 0xfb42ce8f3ffffe73

def z439 : W := mkw 0x05fdea72b0000000 0x00bfbd4e56000000 0xf1fff07830000000 0x7e3ffe0f06000000

def z440 : W := mkw 0x01dd400003514005 0x003ba800006a2800 0xbbe9800003e3e006 0x777d3000007c7c00

def z441 : W := mkw 0x008d400000000000 0x0011a80000000000 0x000ff00000000000 0x6001fe0000000000

def z442 : W := mkw 0x81df54804fdbd8c7 0xd03bea9009fb7b18 0xfbfff0000ffffce6 0x7f7ffe0001ffff9c

def z443 : W := mkw 0x21df70189b5fc10f 0x243bee03136bf821 0xfbfff0783fffe31e 0x7f7ffe0f07fffc63

def z444 : W := mkw 0x4200048806f43f34 0xe840009100de87e6 0x0a0000000ffffffe 0x0140000001ffffff

def z445 : W := mkw 0x0000040804041100 0xa000008100808220 0x401004380c1c0000 0x0802008701838000

def z446 : W := mkw 0xc0ae8dc76da33ef3 0xd815d1b8edb467de 0x77ef8f87cfe37ce7 0xaefdf1f0f9fc6f9c

def z447 : W := mkw 0x03700ae002f00e04 0x406e015c005e01c0 0xbfe00bc003e01f06 0x97fc0178007c03e0

def z448 : W := mkw 0x4020884220202630 0x08041108440404c6 0xa86988463061ef7c 0x550d3108c60c3def

def z449 : W := mkw 0x808e0105490300c3 0x1011c020a9206018 0x758e0f87c00300e1 0xaeb1c1f0f800601c

def z450 : W := mkw 0x80000585448018c0 0xd00000b0a8900318 0x34080f87c0031ce7 0xa68101f0f800639c

def z451 : W := mkw 0xa022bc5afc0e918a 0xb404578b5f81d231 0xf87ffc7ffc1e939b 0xff0fff8fff83d273

def z452 : W := mkw 0x008f5000090bc003 0x0011ea0001217800 0x0006700000000000 0x0000ce0000000000

def z453 : W := mkw 0xa5fffb77f80a808a 0x14bfff6eff015011 0xf5fffffff0028099 0xfebffffffe005013

def z454 : W := mkw 0xa08e3595dd8b98cb 0xd411c6b2bbb17319 0x778e7f87ff839cff 0xeef1cff0fff0739f

def z455 : W := mkw 0x01dd400000000000 0x003ba80000000000 0xf9fff0000063e006 0x7f3ffe00000c7c00

def z456 : W := mkw 0x01700a6000200600 0x002e014c000400c0 0xfdf00ff800601f06 0x9fbe01ff000c03e0

def z457 : W := mkw 0x40ac894720202630 0x08159128e40404c6 0xfdef8fc7f063ffff 0xffbdf1f8fe0c7fff

def z458 : W := mkw 0x05fdcb6720000000 0x00bfb96ce4000000 0xb5e98bc630000001 0xf6bd3178c6000000

def z459 : W := mkw 0xa422bf7ffc0e918a 0xb48457efff81d231 0xdc167ffffc1e939b 0xfb82cfffff83d273

def z460 : W := mkw 0x4020884220202630 0x08041108440404c6 0x2069884630617ffd 0x840d3108c60c2fff

def z461 : W := mkw 0x0000000000000000 0x0000000000000000 0x75800f8000000000 0x8eb001f000000000

def z462 : W := mkw 0xa3723e78de7e978e 0xb46e47cf1bcfd2f1 0xd8767479fc7e939b 0xfb0ece8f3f8fd273

def z463 : W := mkw 0x42208eea24a43f30 0xe84411dd449487e6 0xbc698ffe3063ffff 0xf78d31ffc60c7fff

def z464 : W := mkw 0xc5ffeff7fda33ef3 0xd8bffdfeffb467de 0xffffffffffe3ffff 0xfffffffffffc7fff

def z465 : W := mkw 0x0400a117b0000000 0x00801422f6000000 0x00000007f0000001 0x00000000fe000000

def z466 : W := mkw 0xa48ff117f80a808a 0x1491fe22ff015011 0x000ff007f0028099 0x6001fe00fe005013

def z467 : W := mkw 0x40ac89c721a12e71 0x48159138e43425ce 0x27e98b8603e16c64 0x04fd3170c07c2d8c

def z468 : W := mkw 0x07fdefffb4a41f00 0xe0ffbdfff69483e0 0xf5fffffff0001f01 0xfebffffffe0003e0

def z469 : W := mkw 0x4000800220002030 0x0800100044000406 0x300988063003fcff 0xe6013100c6007f9f

def z470 : W := mkw 0x000210000b5bc007 0x00004200016b7800 0xda1670000fffe006 0x7b42ce0001fffc00

def z471 : W := mkw 0xa00214084f5fd18f 0xb400428109ebfa31 0x0a0000000ffff39e 0x0140000001fffe73

def z472 : W := mkw 0x20003418940c9108 0xa400068312819221 0xd81074783c1c931a 0xdb020e8f07839263

def z473 : W := mkw 0xe0229c4a6c2eb7ba 0xbc0453894d85d6f7 0xb86988463c7fffff 0xf70d3108c78fffff

def z474 : W := mkw 0x4020884220202630 0x08041108440404c6 0x886188463060fff9 0xd10c3108c60c1fff

def z475 : W := mkw 0xa1537418de5ed18e 0xb42a6e831bcbda31 0xd877f479fc7ef39b 0xfb0efe8f3f8fde73

def z476 : W := mkw 0x4020884220202630 0x08041108440404c6 0xb069884630616c65 0xf60d3108c60c2d8c

def z477 : W := mkw 0x0350048806f41f04 0xe06a009100de83e0 0xfbf000000ffc1f06 0x1f7e000001ff83e0

def z478 : W := mkw 0x0150040806541104 0xa02a008100ca8220 0xfbf004780ffc1306 0x9f7e008f01ff8260

def z479 : W := mkw 0x40208c4a24243730 0xa8041189448486e6 0xf8798c7e3c7fffff 0xff0f318fc78fffff

def z480 : W := mkw 0x43708a6a22742734 0x286e114d444e84e6 0xb879887e307fffff 0xf70f310fc60fffff

def z481 : W := mkw 0x0000000000000000 0x0000000000000000 0x1000000000021083 0xa200000000004210

def z482 : W := mkw 0x01700ee004801800 0xc02e01dc00900300 0xf7f00ff80f801c06 0x9efe01ff01f00380

def z483 : W := mkw 0x07fdcfef26f41f04 0xe0ffb9fde4de83e0 0xfff98ffe0ffc1f06 0x9fff31ffc1ff83e0

def z484 : W := mkw 0xa1df54084f5fd18f 0xb43bea8109ebfa31 0xfbfff0000ffff39e 0x7f7ffe0001fffe73

def z485 : W := mkw 0x82200fed44a41fc0 0xf04401fda89483f8 0x04000fffc0001fe1 0x808001fff80003fc

def z486 : W := mkw 0x07fdebf7b2f00e04 0x40ffbd7ef65e01c0 0xf7fffffff3e00c05 0xfefffffffe7c0180

def z487 : W := mkw 0xa3702ef8d6f41f8c 0xf46e05df1ade83f1 0xfff00ff9fffc1f9f 0x9ffe01ff3fff83f3

def z488 : W := mkw 0x81fe0fe54d8318c3 0xd03fc1fca9b06318 0xf7fe0fffcf831ce7 0xbeffc1fff9f0639c

def z489 : W := mkw 0x05fdeff7b4801800 0xc0bfbdfef6900300 0xf7ffffffff801c07 0xfefffffffff00380

def z490 : W := mkw 0x07fdeb7fb2740704 0x20ffbd6ff64e80e0 0xfdfffffff07c0301 0xffbffffffe0f8060

def z491 : W := mkw 0xc0ae8947692326f3 0x1815d128ed2464de 0xb86f8847f063ffff 0xf70df108fe0c7fff

def z492 : W := mkw 0x0200000802740704 0x20400001004e80e0 0x08000000007c0300 0x01000000000f8060

def z493 : W := mkw 0x01ff58400b7bc607 0x003feb08016f78c0 0xfbfff8400fffff06 0xff7fff0801ffffe0

def z494 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0xd8167479cc1c1302 0x9b02ce8f39838260

def z495 : W := mkw 0x0020884220000000 0x0004110844000000 0x8061804030000000 0x500c300806000000

def z496 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0x020e0007cf831ce7 0x2041c000f9f0639c

def z497 : W := mkw 0x4020884220202630 0x08041108440404c6 0xb869884600617f66 0x970d3108c00c2fec

def z498 : W := mkw 0x4020884220202630 0x08041108440404c6 0x986180403062f39b 0xf30c3008060c5e73

def z499 : W := mkw 0x015150000258c004 0x002a2a00004b1800 0x00107000001c0000 0x00020e0000038000

def z500 : W := mkw 0x01df54080f5fd107 0xa03bea8101ebfa20 0xfbfff4780ffff306 0xff7ffe8f01fffe60

def z501 : W := mkw 0x01dd50000359c005 0x003baa00006b3800 0xabf9f00003fde004 0x557f3e00007fbc00

def z502 : W := mkw 0x0020084000200600 0x00040108000400c0 0x0000084000001f00 0x80000108000003e0

def z503 : W := mkw 0x808f5105490bc0c3 0x1011ea20a9217818 0x000ff007c003e0e1 0x6001fe00f8007c1c

def z504 : W := mkw 0x20023018980e810a 0x240046031301d021 0xd81670783c1e831a 0x7b02ce0f0783d063

def z505 : W := mkw 0x4020884220202630 0x08041108440404c6 0x886180403063fffe 0x510c3008060c7fff

def z506 : W := mkw 0x4000000000202630 0x08000000000404c6 0x380808060063ffff 0xa7010100c00c7fff

def z507 : W := mkw 0x0000000000000000 0x0000000000000000 0x738000000f800006 0x0e70000001f00000

def z508 : W := mkw 0xa2202ef8d4a41f88 0xf44405df1a9483f1 0x04000ff9f0001f99 0x808001ff3e0003f3

def z509 : W := mkw 0x4000800220002030 0x0800100044000406 0x980980463003f3fb 0xf3013008c6007e7f

def z510 : W := mkw 0x800204804d8318c3 0xd000409009b06318 0x320808060f831ce7 0xa6410100c1f0639c

def z511 : W := mkw 0xa5ffff7ffc0e918a 0xb4bfffefff81d231 0xf5fffffffc1c0001 0xfebfffffff838000

def z512 : W := mkw 0x0020084000200600 0x00040108000400c0 0xb860084030629f9f 0xf70c0108060c53f3

def z513 : W := mkw 0x40ae884229232633 0x0815d108452464c6 0xfbef88463fe3ffff 0xff7df108c7fc7fff

def z514 : W := mkw 0x4020884220002030 0x0804110844000406 0xb06988463003e0f9 0xf60d3108c6007c1f

def z515 : W := mkw 0x008c018501810841 0x40118030a0302108 0x37880b8603831ce7 0xa6f10170c070639c

def z516 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0xa5f9fbfe30000000 0x54bf3f7fc6000000

def z517 : W := mkw 0xa08e359ddd8f99cb 0xf411c6b3bbb1f339 0xdf9677f9ff9e939b 0xfbf2ceff3ff3d273

def z518 : W := mkw 0x00200c4804241700 0xa0040189008482e0 0xf8700c780c7c1f06 0x9f0e018f018f83e0

def z519 : W := mkw 0x402298422b7be637 0x08045308456f7cc6 0xba6988463fffffff 0xf74d3108c7ffffff

def z520 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0x25effb87f0000001 0x64bdff70fe000000

def z521 : W := mkw 0xa3723ef8defe9f8e 0xf46e47df1bdfd3f1 0xfff67ff9cffc1f06 0x9ffecfff39ff83e0

def z522 : W := mkw 0x01700a6000000000 0x002e014c00000000 0x8070007800000000 0x100e000f00000000

def z523 : W := mkw 0x01df54800fdbd807 0xc03bea9001fb7b00 0xffffff800ffffc06 0xfffffff001ffff80

def z524 : W := mkw 0x800204804c821882 0xd000409009904310 0x77860f81cf821c87 0xaef0c1f039f04390

def z525 : W := mkw 0x4020884220202630 0x08041108440404c6 0x3008084630031fff 0xa6010108c60063ff

def z526 : W := mkw 0x21517018925cc10c 0x242a2e03124b9821 0x8871f078307ce318 0x510e3e0f060f9c63

def z527 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0x77860f81cf801c06 0x8ef0c1f039f00380

def z528 : W := mkw 0x00ac894720000000 0x00159128e4000000 0xf5ef8fc7f0000001 0xfebdf1f8fe000000

def z529 : W := mkw 0x41ffd8422b7be637 0x083ffb08456f7cc6 0xfbfff0403fffe31e 0x7f7ffe0807fffc63

def z530 : W := mkw 0x20003018900c8108 0x2400060312019021 0x00107038001c0000 0x00020e0700038000

def z531 : W := mkw 0x05fdcb6723514005 0x00bfb96ce46a2800 0x27e98b8603e16004 0x04fd3170c07c2c00

def z532 : W := mkw 0x87ffeffffff71fc7 0xf0fffdfffffee3f8 0xffffffffffff1fe7 0xffffffffffffe3fc

def z533 : W := mkw 0xe022bc5afc2eb7ba 0xbc04578b5f85d6f7 0xd877f479fc7ef39b 0xfb0efe8f3f8fde73

def z534 : W := mkw 0x85fffff7ffdbd8c7 0xd0bffffefffb7b18 0xfffffffffffffce7 0xffffffffffffff9c

def z535 : W := mkw 0xc0ae8dc76da33ef3 0xd815d1b8edb467de 0x778e0fc7ff831fff 0xaef1c1f8fff063ff

def z536 : W := mkw 0x03715ee806fcdf04 0xe06e2bdd00df9be0 0xfff1fff80ffcff06 0xdffe3fff01ff9fe0

def z537 : W := mkw 0x03700a6802740704 0x206e014d004e80e0 0xb8700878007c1f06 0x970e010f000f83e0

def z538 : W := mkw 0x00021000080a8002 0x0000420001015000 0x0006700000028000 0x6000ce0000005000

def z539 : W := mkw 0x4020884220202630 0x08041108440404c6 0xb86988060063ec66 0x770d3100c00c7d8c

def z540 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0x8a7000780ffc1f06 0x114e000f01ff83e0

def z541 : W := mkw 0x01fdc84220000000 0x003fb90844000000 0xf1fff84630000001 0xfe3fff08c6000000

def z542 : W := mkw 0x008f50000b5bc007 0x0011ea00016b7800 0x0a0ff0000fffe006 0x6141fe0001fffc00

def z543 : W := mkw 0x4020884220202630 0x08041108440404c6 0x886980463063e3f9 0x710d3008c60c7c7f

def z544 : W := mkw 0xa000040844041188 0xb400008108808231 0x0000000000001398 0x0000000000000273

def z545 : W := mkw 0x4020884220202630 0x08041108440404c6 0x9800084630029ffb 0xf3000108c60053ff

def z546 : W := mkw 0x01dd400003514005 0x003ba800006a2800 0xfbf980000ffd6006 0x1f7f300001ffac00

def z547 : W := mkw 0x800204004c021082 0x9000408009804210 0x000000000c021082 0x0000000001804210

def z548 : W := mkw 0x4020884220202630 0x08041108440404c6 0xb86188403060ff1e 0xd70c3108060c1fe3

def z549 : W := mkw 0x83720ee84ff71fc7 0xf06e41dd09fee3f8 0xfff00ff80fff1fe6 0x9ffe01ff01ffe3fc

def z550 : W := mkw 0xe0aebddffdafbffb 0xfc15d7bbffb5f7ff 0xffffffffffffffff 0xffffffffffffffff

def z551 : W := mkw 0x03700e6806741704 0xa06e01cd00ce82e0 0xd87004780c7c1302 0x9b0e008f018f8260

def z552 : W := mkw 0xa00214084c0e918a 0xb40042810981d231 0x58060401cc1e939b 0xab00c0803983d273

def z553 : W := mkw 0x0420aa72b0000000 0x0084154e56000000 0x0000007830000000 0x0000000f06000000

def z554 : W := mkw 0x41708a6220202630 0x082e114c440404c6 0xfdf98ffe3063ffff 0xffbf31ffc60c7fff

def z555 : W := mkw 0x0000048004801800 0xc000009000900300 0x04000f8000001c00 0x808001f000000380

def z556 : W := mkw 0x02200ee806f41f04 0xe04401dd00de83e0 0x0e000ff80ffc1f06 0x81c001ff01ff83e0

def z557 : W := mkw 0x03700a6002700604 0x006e014c004e00c0 0x0060000000600000 0x000c0000000c0000

def z558 : W := mkw 0x0000000000000000 0x0000000000000000 0xb808084630039fff 0xf7010108c60073ff

def z559 : W := mkw 0x02200ee804a41f00 0xe04401dd009483e0 0xbc600ff800601f06 0x978c01ff000c03e0

def z560 : W := mkw 0xc0208dc764a03ef0 0xd80411b8ec9407de 0xbc698fc7f063ffff 0xf78d31f8fe0c7fff

def z561 : W := mkw 0x0020884220200600 0x00041108440400c0 0xb869884630601f07 0xf70d3108c60c03e0

def z562 : W := mkw 0x81de05854fd318c7 0xd03bc0b0a9fa6318 0xfffe0f87cfff1ce7 0xbfffc1f0f9ffe39c

def z563 : W := mkw 0x05fdfb77b258c004 0x00bfbf6ef64b1800 0xfdfffffff07ce001 0xffbffffffe0f9c00

def z564 : W := mkw 0x83fe0fe54ff31ec7 0xd07fc1fca9fe63d8 0x77ee0f87cfe31ce7 0xaefdc1f0f9fc639c

def z565 : W := mkw 0x4020884220202630 0x08041108440404c6 0xb860084630601fff 0x970c0108c60c03ff

def z566 : W := mkw 0x4171d8422278e634 0x082e3b08444f1cc6 0x8871f040307ce318 0x510e3e08060f9c63

def z567 : W := mkw 0x01708a6220000000 0x002e114c44000000 0xf5f98ffe30000001 0xfebf31ffc6000000

def z568 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0x887ff000007fe000 0x710ffe00000ffc00

def z569 : W := mkw 0x0571ea72b0000000 0x00ae3d4e56000000 0xf5f1fff830000000 0xdebe3fff06000000

def z570 : W := mkw 0x45fdeb77b0202630 0x08bfbd6ef60404c6 0xf5fffffff0616c65 0xfebffffffe0c2d8c

def z571 : W := mkw 0x4000800220002030 0x0800100044000406 0xb86980063063e0ff 0x770d3000c60c7c1f

def z572 : W := mkw 0x0000000000000000 0x0000000000000000 0x9800000000028002 0x7300000000005000

def z573 : W := mkw 0x0000000000200600 0x00000000000400c0 0x0800000000601f06 0x01000000000c03e0

def z574 : W := mkw 0x40ac89c721a12e71 0x48159138e43425ce 0xbfe98bc633e3ffff 0xf7fd3178c67c7fff

def z575 : W := mkw 0x41ffd8422b7be637 0x083ffb08456f7cc6 0xfbfff8060fffec66 0x7f7fff00c1fffd8c

def z576 : W := mkw 0xa1df7418df5fd18f 0xb43bee831bebfa31 0xfbfff439cfffe006 0x7f7ffe8739fffc00

def z577 : W := mkw 0xa1723e78dc0e918a 0xb42e47cf1b81d231 0xfdf67ff9fc1e939b 0xffbecfff3f83d273

def z578 : W := mkw 0x0200048806d41904 0xe040009100da8320 0x020000000f9c0000 0x0040000001f38000

def z579 : W := mkw 0x035006a806f41f04 0xe06a00d500de83e0 0x4f9007b80ffc1f06 0x09f200f701ff83e0

def z580 : W := mkw 0x4020884220202630 0x08041108440404c6 0xb86988463060e319 0xf70d3108c60c1c63

def z581 : W := mkw 0x008e000009030003 0x0011c00001206000 0xfbef80000fe3e006 0x7f7df00001fc7c00

def z582 : W := mkw 0x008e000009030003 0x0011c00001206000 0x738e08060f831ce7 0xae71c100c1f0639c

def z583 : W := mkw 0x03df56a80fdfd907 0xe07bead501fbfb20 0xfffff7b80fffe006 0x7ffffef701fffc00

def z584 : W := mkw 0x800214004c0a9082 0x9000428009815210 0xd8167401cc1e9083 0xfb02ce803983d210

def z585 : W := mkw 0x01df40000b534007 0x003be800016a6800 0x73ef80000fe36006 0x2e7df00001fc6c00

def z586 : W := mkw 0x0000000000000000 0x0000000000000000 0xb86988060063fce7 0xf70d3100c00c7f9c

def z587 : W := mkw 0x03700ae002f00e04 0x406e015c005e01c0 0xf7f00ff803e00c04 0x9efe01ff007c0180

def z588 : W := mkw 0x0150000002500004 0x002a0000004a0000 0x88700000007c0000 0x110e0000000f8000

def z589 : W := mkw 0x02200a6800240700 0x2044014d000480e0 0x0000007800000300 0x0000000f00000060

def z590 : W := mkw 0xa2223ef8dcae9f8a 0xf44447df1b95d3f1 0xdc167ff9fc1e9f9b 0xfb82cfff3f83d3f3

def z591 : W := mkw 0xa0023410dc0a908a 0x940046821b815211 0x50067401fc02909b 0xea00ce803f805213

def z592 : W := mkw 0x828e058d4ff71fc7 0xf051c0b1a9fee3f8 0x7f8e0f87cfff1fe7 0xaff1c1f0f9ffe3fc

def z593 : W := mkw 0xa1df7010db5bc08f 0x143bee021b6b7811 0xfbfff001ffffe09f 0x7f7ffe003ffffc13

def z594 : W := mkw 0x0000000000000000 0x0000000000000000 0x3008080600000001 0xa6010100c0000000

def z595 : W := mkw 0x808e15854fdbd8c7 0xd011c2b0a9fb7b18 0x7f8e0f87cffffce7 0xaff1c1f0f9ffff9c

def z596 : W := mkw 0x4000800220002030 0x0800100044000406 0x000180003000e018 0x4000300006001c03

def z597 : W := mkw 0x03fc0fed07f51f45 0xe07f81fda0fea3e8 0xfff80ffe0ffd1f66 0x9fff01ffc1ffa3ec

def z598 : W := mkw 0x048de117b0000000 0x0091bc22f6000000 0xd01ff47ff0000001 0xfa03fe8ffe000000

def z599 : W := mkw 0x85df67b5dd8318c3 0xd0bbecf6bbb06318 0x779e7fbfcf831ce7 0xaef3cff7f9f0639c

def z600 : W := mkw 0x0000000000000000 0x0000000000000000 0xb86980403063f39f 0xf70d3008060c7e73

def z601 : W := mkw 0x008c010501010041 0x00118020a0202008 0x0008000600010060 0x00010000c000200c

def z602 : W := mkw 0x0000048004801800 0xc000009000900300 0x020000000f801c06 0x0040000001f00380

def z603 : W := mkw 0x048dc10720000000 0x0091b820e4000000 0x0009800600000000 0x00013000c0000000

def z604 : W := mkw 0x23703a78927c870c 0x246e074f124f90e1 0x88707078307c8318 0x510e0e0f060f9063

def z605 : W := mkw 0x42208cca26f43f34 0xe844119944de87e6 0xba6988463fffffff 0xf74d3108c7ffffff

def z606 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0xd8167439cc1e8002 0x7b02ce873983d000

def z607 : W := mkw 0xe020ac5af42437b8 0xbc04158b5e8486f7 0xb8698c7ff063ffff 0xf70d318ffe0c7fff

def z608 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0x439ff0000f9fe000 0x6873fe0001f3fc00

def z609 : W := mkw 0x0000000000000000 0x0000000000000000 0xb860000000600006 0x170c0000000c0000

def z610 : W := mkw 0x4020884220202630 0x08041108440404c6 0xb86980403063e31e 0x770d3008060c7c63

def z611 : W := mkw 0x808e04004d031083 0x9011c08009a06210 0x738e0401cf831087 0xae71c08039f06210

def z612 : W := mkw 0x04ade957b0000000 0x0095bd2af6000000 0xb06ff847f0000001 0xf60dff08fe000000

def z613 : W := mkw 0x808c0585448018c0 0xd01180b0a8900318 0x758e0f87c0001ce1 0xaeb1c1f0f800039c

def z614 : W := mkw 0x0000018500800840 0x40000030a0100108 0x04000b8600000c60 0x00800170c000018c

def z615 : W := mkw 0xa0223c58dc2e978a 0xb404478b1b85d2f1 0xf8767c79fc7e9f9f 0xff0ecf8f3f8fd3f3

def z616 : W := mkw 0x0000201090000000 0x0000040212000000 0xd8167479f002939b 0xfb02ce8f3e005273

def z617 : W := mkw 0x0401e012b0000000 0x00803c0256000000 0x0001f00030000000 0x40003e0006000000

def z618 : W := mkw 0x0000040804041100 0xa000008100808220 0x0000047800001300 0x8000008f00000260

def z619 : W := mkw 0x0000201090000000 0x0000040212000000 0x00067001f0000001 0x6000ce003e000000

def z620 : W := mkw 0x800204084c061182 0xb00040810980c230 0xd8160479cc1e1383 0xbb02c08f3983c270

def z621 : W := mkw 0x808e0105490300c3 0x1011c020a9206018 0x738e0007cf8300e7 0x2e71c000f9f0601c

def z622 : W := mkw 0x00200cc004a01e00 0xc0040198009403c0 0xffe00fc00fe01f06 0x9ffc01f801fc03e0

def z623 : W := mkw 0xa0002010d0000088 0x140004021a000011 0x00000001f0000099 0x000000003e000013

def z624 : W := mkw 0x01700a6000000000 0x002e014c00000000 0x25e00b8000000000 0x04bc017000000000

def z625 : W := mkw 0x2000301090088008 0x0400060212011001 0x0000700030008018 0x40000e0006001003

def z626 : W := mkw 0x4000000000202630 0x08000000000404c6 0x980000403063ffff 0xf3000008060c7fff

def z627 : W := mkw 0x81df54004f5bd087 0x903bea8009eb7a10 0xfbfff401cffff087 0xff7ffe8039fffe10

def z628 : W := mkw 0x41fdc84220202630 0x083fb908440404c6 0xf9fff8463063ffff 0xff3fff08c60c7fff

def z629 : W := mkw 0x408fd002290be033 0x0811fa0045217c06 0x000ff0063003e0f9 0x6001fe00c6007c1f

def z630 : W := mkw 0x01dd601090000000 0x003bac0212000000 0xf1fff479f0000001 0xfe3ffe8f3e000000

def z631 : W := mkw 0x0150000002500004 0x002a0000004a0000 0xfbf980000fffe006 0x7f7f300001fffc00

def z632 : W := mkw 0xe002b41afc0eb1ba 0xbc0056835f81d637 0xd81ff47ffc1ff3fb 0xfb03fe8fff83fe7f

def z633 : W := mkw 0x01df70109b5bc007 0x003bee02136b7800 0xfbfff479ffffe007 0xff7ffe8f3ffffc00

def z634 : W := mkw 0x2571fa7ab00c8108 0x24ae3f4f56019021 0x8871f078301c8318 0x510e3e0f06039063

def z635 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0x27e00ff803e01f04 0x84fc01ff007c03e0

def z636 : W := mkw 0x05fdebf7b1810841 0x40bfbd7ef6302108 0xf7fffffff3810c65 0xfefffffffe70218c

def z637 : W := mkw 0x008f5000090bc003 0x0011ea0001217800 0x738ff0000f83e006 0x6e71fe0001f07c00

def z638 : W := mkw 0x0200048806f41f04 0xe040009100de83e0 0x7f800f800ffc1f06 0x8ff001f001ff83e0

def z639 : W := mkw 0x4020a852b0202630 0x0804150a560404c6 0xf87ffc7ff063ffff 0xff0fff8ffe0c7fff

def z640 : W := mkw 0x4171d8422278e634 0x082e3b08444f1cc6 0xb879f846307fffff 0xf70f3f08c60fffff

def z641 : W := mkw 0x0000100000088000 0x0000020000011000 0x88107000001c8000 0x51020e0000039000

def z642 : W := mkw 0x008c058504801800 0xc01180b0a0900300 0x778e0f87cf801c07 0xaef1c1f0f9f00380

def z643 : W := mkw 0x05dff117bb5bc007 0x00bbfe22f76b7800 0xfbfff007ffffe007 0x7f7ffe00fffffc00

def z644 : W := mkw 0x015210000b5bc007 0x002a4200016b7800 0xfbf000000fffe006 0x1f7e000001fffc00

def z645 : W := mkw 0x820204884ff71fc7 0xf040409109fee3f8 0x0a0000000fff1fe6 0x0140000001ffe3fc

def z646 : W := mkw 0x0771eefab6f41f04 0xe0ee3ddf56de83e0 0xfff1fff83ffc1f06 0xdffe3fff07ff83e0

def z647 : W := mkw 0x800204804d8318c3 0xd000409009b06318 0x52060401cf831ce7 0xaa40c08039f0639c

def z648 : W := mkw 0x23703ef896fc9f0c 0xe46e07df12df93e1 0xfff07ff83ffc9f1e 0xdffe0fff07ff93e3

def z649 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0x8c700ff8007c1f00 0x918e01ff000f83e0

def z650 : W := mkw 0x07fdcbe722f00e04 0x40ffb97ce45e01c0 0x27e98b8603e00c04 0x04fd3170c07c0180

def z651 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000030028099 0x6000000006005013

def z652 : W := mkw 0x0020084000200600 0x00040108000400c0 0xb86988400063ff06 0xf70d3108000c7fe0

def z653 : W := mkw 0xa00214084c0e918a 0xb40042810981d231 0xd81004780c1e939a 0x9b02008f0183d273

def z654 : W := mkw 0x83de07ad4fd719c7 0xf07bc0f5a9fae338 0x479607b9cf9c0000 0x08f2c0f739f38000

def z655 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0xf3fff0000f9c0000 0x7e7ffe0001f38000

def z656 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0x25e98ffff0000001 0x84bd31fffe000000

def z657 : W := mkw 0x41fdc84223716635 0x083fb908446e2cc6 0x23e9880603e16c64 0x047d3100c07c2d8c

def z658 : W := mkw 0x0151400000000000 0x002a280000000000 0x8071f00000000000 0x500e3e0000000000

def z659 : W := mkw 0x03721ee80fffdf07 0xe06e43dd01fffbe0 0xfff00ff80fffff06 0x9ffe01ff01ffffe0

def z660 : W := mkw 0x800214804fdbd8c7 0xd000429009fb7b18 0x0a0000000ffffce6 0x0140000001ffff9c

def z661 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000031ce6 0x000000000000639c

def z662 : W := mkw 0xe022b852f82aa6ba 0x1c04570a5f0554d7 0xb86ff847f063ffff 0xf70dff08fe0c7fff

def z663 : W := mkw 0x8000040044001080 0x9000008008800210 0x00000401c0001081 0x8000008038000210

def z664 : W := mkw 0x4020084000202630 0x08040108000404c6 0xb86008400063fffe 0x970c0108000c7fff

def z665 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0x00067479f0029399 0xe000ce8f3e005273

def z666 : W := mkw 0x008c000001010001 0x0011800000202000 0x2388000003810004 0x0471000000702000

def z667 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0x478e0787cf8300e1 0x28f1c0f0f9f0601c

def z668 : W := mkw 0x05ffdb672b5bc007 0x00bffb6ce56b7800 0xfffffb860fffe006 0x7fffff70c1fffc00

def z669 : W := mkw 0x80020000490300c3 0x1000400009206018 0x00000000000300e0 0x000000000000601c

def z670 : W := mkw 0x03fc0be503f10e45 0x407f817ca07e21c8 0x27e80b8603e10c64 0x04fd0170c07c218c

def z671 : W := mkw 0x80000105400000c0 0x10000020a8000018 0x00000007c00000e1 0x00000000f800001c

def z672 : W := mkw 0xa3ff7ef8dfffdf8f 0xf47fefdf1bfffbf1 0xfffffff9ffffff9f 0xffffffff3ffffff3

def z673 : W := mkw 0x03721ee80efe9f06 0xe06e43dd01dfd3e0 0xfff67ff80ffe9f06 0xfffecfff01ffd3e0

def z674 : W := mkw 0x4000000000202630 0x08000000000404c6 0x0000000000616c64 0x00000000000c2d8c

def z675 : W := mkw 0xc0208dc764a03ef0 0xd80411b8ec9407de 0x04000fc7f0001ff9 0x808001f8fe0003ff

def z676 : W := mkw 0xa0003418d40c9188 0xb40006831a819231 0x88107479f01c9399 0xd1020e8f3e039273

def z677 : W := mkw 0x0000008000800800 0x4000001000100100 0x27800b8003800c04 0x04f0017000700180

def z678 : W := mkw 0x03ff5a680b7fc707 0x207feb4d016ff8e0 0xfbfff0780fffe306 0x7f7ffe0f01fffc60

def z679 : W := mkw 0x008c010500000000 0x00118020a0000000 0x000e0007c0000001 0x2001c000f8000000

def z680 : W := mkw 0x40208cc224a03e30 0xc8041198449407c6 0xffe98fc63fe3ffff 0xfffd31f8c7fc7fff

def z681 : W := mkw 0x0150000000000000 0x002a000000000000 0xf1f0000000000000 0x1e3e000000000000

def z682 : W := mkw 0x03fc0fed06f41f04 0xe07f81fda0de83e0 0xfffe0fffcffc1f07 0xbfffc1fff9ff83e0

def z683 : W := mkw 0x4020884220202630 0x08041108440404c6 0x0061800000606000 0x000c3000000c0c00

def z684 : W := mkw 0x800205854d8318c3 0xd00040b0a9b06318 0x06000f87cf831ce7 0x80c001f0f9f0639c

def z685 : W := mkw 0x43708ae222f02e34 0x486e115c445e05c6 0xbfe98bc633e3ffff 0xf7fd3178c67c7fff

def z686 : W := mkw 0x0571ea72b0000000 0x00ae3d4e56000000 0xb079f87e30000001 0xf60f3f0fc6000000

def z687 : W := mkw 0x6020b85ab02ca738 0x2c04170b560594e7 0x8871f078307ce318 0x510e3e0f060f9c63

def z688 : W := mkw 0x000010000258c004 0x00000200004b1800 0x08000000007ce000 0x01000000000f9c00

def z689 : W := mkw 0x01dd410500000000 0x003ba820a0000000 0xf5ffff87c0000001 0xfebffff0f8000000

def z690 : W := mkw 0xa1df7418df5fd18f 0xb43bee831bebfa31 0x43967439cf9c0000 0x0872ce8739f38000

def z691 : W := mkw 0x85ffef77fc021082 0x90bffdeeff804210 0xf5fffffffc021083 0xfebfffffff804210

def z692 : W := mkw 0x04acab77b0000000 0x0095956ef6000000 0x758e0ffff0000001 0xaeb1c1fffe000000

def z693 : W := mkw 0xa08e351ddd0f91cb 0xb411c6a3bba1f239 0xd81e747ffc1f93fb 0xfb03ce8fff83f27f

def z694 : W := mkw 0x008d400001014001 0x0011a80000202800 0x0009800000016000 0x0001300000002c00

def z695 : W := mkw 0x0000000000000000 0x0000000000000000 0x9000004030000001 0xf200000806000000

def z696 : W := mkw 0x41df50000b7be637 0x083bea00016f7cc6 0xfbfff0000ffffffe 0x7f7ffe0001ffffff

def z697 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0x08000479fc1e939b 0x8100008f3f83d273

def z698 : W := mkw 0x4000800220002030 0x0800100044000406 0x0009800600016060 0x00013000c0002c0c

def z699 : W := mkw 0x01dd400003514005 0x003ba800006a2800 0x0380000003800000 0x0070000000700000

def z700 : W := mkw 0x0000800220000000 0x0000100044000000 0x0009800630000001 0x60013000c6000000

def z701 : W := mkw 0x03700ee006f01e04 0xc06e01dc00de03c0 0x77e00f800fe01c06 0x8efc01f001fc0380

def z702 : W := mkw 0xa0023010d80a808a 0x140046021b015011 0xd0167479f0028099 0xfa02ce8f3e005013

def z703 : W := mkw 0x0770afffb6f41f04 0xe0ee15fff6de83e0 0xfff00ffffffc1f07 0x9ffe01ffffff83e0

def z704 : W := mkw 0x848fe597fd8318c3 0xd091fcb2ffb06318 0x778fff87ff831ce7 0xeef1fff0fff0639c

def z705 : W := mkw 0x41dfd0022b5be037 0x083bfa00456b7c06 0xfbfff0063fffe0ff 0x7f7ffe00c7fffc1f

def z706 : W := mkw 0xa5df773ddc0e918a 0xb4bbeee7bb81d231 0x459677b9cc1c0000 0x08b2cef739838000

def z707 : W := mkw 0x01708a6222500004 0x002e114c444a0000 0xfff98ffe3fffe007 0xffff31ffc7fffc00

def z708 : W := mkw 0x848ff117f90bc0c3 0x1091fe22ff217818 0x000ff007f003e0e1 0x6001fe00fe007c1c

def z709 : W := mkw 0xa1dd6418d755518d 0xb43bac831aeaaa31 0x23e98479f3e1739d 0x847d308f3e7c2e73

def z710 : W := mkw 0x035006a806d41904 0xe06a00d500da8320 0xdf9007f83f9e939b 0xfbf200ff07f3d273

def z711 : W := mkw 0x008f50000b5bc007 0x0011ea00016b7800 0xba6ff0000fffe006 0x774dfe0001fffc00

def z712 : W := mkw 0xc0ae8dc76da33ef3 0xd815d1b8edb467de 0xcfe787c1ffe0e318 0x59fcf0f83ffc1c63

def z713 : W := mkw 0x45fdcb6723716635 0x08bfb96ce46e2cc6 0x27e98b8603e16c64 0x04fd3170c07c2d8c

def z714 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0x459677f9f0000000 0x08b2ceff3e000000

def z715 : W := mkw 0x435086aa26d43934 0xe86a10d544da8726 0x479987be3f9fe0f9 0x68f330f7c7f3fc1f

def z716 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0xf5fffffff0028099 0xfebffffffe005013

def z717 : W := mkw 0x03700ee806d41904 0xe06e01dd00da8320 0xfff00ff80f9c1302 0x9ffe01ff01f38260

def z718 : W := mkw 0x035006a806d41904 0xe06a00d500da8320 0xcff007b80ffc0000 0x19fe00f701ff8000

def z719 : W := mkw 0x008c018501810841 0x40118030a0302108 0x678e0f87c3810c64 0x0cf1c1f0f870218c

def z720 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0x7f8e0f87cf839fff 0xaff1c1f0f9f073ff

def z721 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0x88167479f01e9399 0xf102ce8f3e03d273

def z722 : W := mkw 0x02af5ee80dafdf03 0xe055ebdd01b5fbe0 0x040ffff80003ff00 0xe081ffff00007fe0

def z723 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0x77900ff80f9c1f06 0x8ef201ff01f383e0

def z724 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0xfff80ffe0ffc1f07 0xbfff01ffc1ff83e0

def z725 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0xfff00ff80ffe9f9e 0x9ffe01ff01ffd3f3

def z726 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0xdff007f80ffc1302 0x9bfe00ff01ff8260

def z727 : W := mkw 0x4020884220202630 0x08041108440404c6 0x886988463063fff9 0xf10d3108c60c7fff

def z728 : W := mkw 0x44adeb77b0202630 0x0895bd6ef60404c6 0x040ffffff003fff9 0xe081fffffe007fff

def z729 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0xf7ef8f87cf831ce7 0xfefdf1f0f9f0639c

def z730 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0xfff00ff83ffc1f9f 0x9ffe01ff07ff83f3

def z731 : W := mkw 0x01dd400003514005 0x003ba800006a2800 0xfbfff0000ffd6006 0x7f7ffe0001ffac00

def z732 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0xfbfff0060fffe0e7 0x7f7ffe00c1fffc1c

def z733 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0xfbfff0403fffe31e 0x7f7ffe0807fffc63

def z734 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0xf5fffffff0001c07 0xfebffffffe000380

def z735 : W := mkw 0x008e010509030003 0x0011c020a1206000 0x778e0f87cf831ce7 0xaef1c1f0f9f0639c

def z736 : W := mkw 0x20003018900c8108 0x2400060312019021 0xc8167479f01c8318 0x5902ce8f3e039063

def z737 : W := mkw 0x808e058d4d8719c3 0xf011c0b1a9b0e338 0x779e0fbfcf9f1ce7 0xaef3c1f7f9f3e39c

def z738 : W := mkw 0x07fdeb77b2700604 0x00ffbd6ef64e00c0 0xf5fffffff0600001 0xfebffffffe0c0000

def z739 : W := mkw 0x05fdeb77b1010041 0x00bfbd6ef6202008 0xf5fffffff0010061 0xfebffffffe00200c

def z740 : W := mkw 0x808c0185418108c1 0x50118030a8302118 0x27880b87c3810ce5 0x04f10170f870219c

def z741 : W := mkw 0xa5ffdf6f6c0e918a 0xb4bffbeded81d231 0x2de98b860c1e939a 0x05bd3170c183d273

def z742 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0xf5fffffff0021083 0xfebffffffe004210

def z743 : W := mkw 0x035006a806d41904 0xe06a00d500da8320 0xf7f007b80f9c0000 0x1efe00f701f38000

def z744 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0xfbfff8000ffffc06 0xff7fff0001ffff80

def z745 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0x7f8e0f87cfe3fce7 0xaff1c1f0f9fc7f9c

def z746 : W := mkw 0x05dd633590000000 0x00bbac66b2000000 0xf5ffffbfc0000001 0xfebffff7f8000000

def z747 : W := mkw 0x05fdeb77b0200600 0x00bfbd6ef60400c0 0xfdfffffff0629f9f 0xffbffffffe0c53f3

def z748 : W := mkw 0x03700ae802f40f04 0x606e015d005e81e0 0xfff00bf80ffc0f06 0x1ffe017f01ff81e0

def z749 : W := mkw 0x035006a806d41904 0xe06a00d500da8320 0x77980fbe0f9f1ce7 0xaef301f7c1f3e39c

def z750 : W := mkw 0x00023010980a8002 0x0000460213015000 0xd8167479fc1e939b 0xfb02ce8f3f83d273

def z751 : W := mkw 0x4771ea7ab2742734 0x28ee3d4f564e84e6 0x8871f078307ce318 0x510e3e0f060f9c63

def z752 : W := mkw 0x8573eef2fd8318c3 0xd0ae7dde5fb06318 0x8271f0783f831ce6 0x504e3e0f07f0639c

def z753 : W := mkw 0x45fdeb77b0202630 0x08bfbd6ef60404c6 0xf5fffffff0637ce7 0xfebffffffe0c6f9c

def z754 : W := mkw 0x808e0185498308c3 0x5011c030a9306118 0x778e0b87cf830ce7 0x2ef1c170f9f0619c

def z755 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0xfff98ffe0fffffe7 0xffff31ffc1fffffc

def z756 : W := mkw 0x01702a7090200600 0x002e054e120400c0 0xfdf67ff9f0629f9f 0xffbecfff3e0c53f3

def z757 : W := mkw 0x448ff117b90be033 0x0891fe22f7217c06 0x000ff007f003e0f9 0x6001fe00fe007c1f

def z758 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0xfff007f80ffc0306 0x1ffe00ff01ff8060

def z759 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0xf79e0fffcf831ce7 0xbef3c1fff9f0639c

def z760 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0x778e0f87ff839cff 0xeef1c1f0fff0739f

def z761 : W := mkw 0x45fdeb77b0002030 0x08bfbd6ef6000406 0xf5fffffff0016061 0xfebffffffe002c0c

def z762 : W := mkw 0x03708eea26f41f04 0xe06e11dd44de83e0 0xfff18ff83ffc1f06 0xdffe31ff07ff83e0

def z763 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0xfd967ff9fc1e939b 0xffb2cfff3f83d273

def z764 : W := mkw 0x05fd6b7590000000 0x00bfad6eb2000000 0xf5fe7fffc0000001 0xbebfcffff8000000

def z765 : W := mkw 0x05df53250b5bc007 0x00bbea64a16b7800 0xfffff3800fffe006 0x7ffffe7001fffc00

def z766 : W := mkw 0x0200048806f41f04 0xe040009100de83e0 0xff900ff80ffc1f06 0x9ff201ff01ff83e0

def z767 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0xfff00ff80ffe1f87 0xbffe01ff01ffc3f0

def z768 : W := mkw 0x04adeb77b0000000 0x0095bd6ef6000000 0xd41ffffff0000001 0xfa83fffffe000000

def z769 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0xfbfff0400ffff306 0xff7ffe0801fffe60

def z770 : W := mkw 0x04adeb77b0000000 0x0095bd6ef6000000 0xb46ffffff0000001 0xf68dfffffe000000

def z771 : W := mkw 0x4020884220202630 0x08041108440404c6 0xf86f8c47f063ffff 0xff0df188fe0c7fff

def z772 : W := mkw 0xe00214884dafbffb 0xfc00429109b5f7ff 0x0a0000000ffffffe 0x0140000001ffffff

def z773 : W := mkw 0x45fdeb77b0202630 0x08bfbd6ef60404c6 0xfdfffffff060fff9 0xffbffffffe0c1fff

def z774 : W := mkw 0xa08e158d4d8f99cb 0xf411c2b1a9b1f339 0xff8e0fc7ff9f9fff 0xfff1c1f8fff3f3ff

def z775 : W := mkw 0x45dd633590202630 0x08bbac66b20404c6 0x4d9677b9c063fffe 0x09b2cef7380c7fff

def z776 : W := mkw 0x808c0585458118c1 0xd01180b0a8b02318 0x37880f87c3831ce7 0xa6f101f0f870639c

def z777 : W := mkw 0x4020884220202630 0x08041108440404c6 0xa86988463063fffe 0x550d3108c60c7fff

def z778 : W := mkw 0x45fdeb77b0202630 0x08bfbd6ef60404c6 0xfdfffffff063e31f 0xffbffffffe0c7c63

def z779 : W := mkw 0x81df51054b5bc0c7 0x103bea20a96b7818 0xfbfff807cffffce7 0xff7fff00f9ffff9c

def z780 : W := mkw 0x0150223090000000 0x002a044612000000 0xd59677f9f0000001 0xfab2ceff3e000000

def z781 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0xf5fffffff0616005 0xfebffffffe0c2c00

def z782 : W := mkw 0x05fdeb77b2500004 0x00bfbd6ef64a0000 0xffffffffffffe007 0xfffffffffffffc00

def z783 : W := mkw 0x015150000258c004 0x002a2a00004b1800 0xcbf1f0000ffce000 0x597e3e0001ff9c00

def z784 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0x63fff0000fffe004 0x6c7ffe0001fffc00

def z785 : W := mkw 0x45fdeb77b0002030 0x08bfbd6ef6000406 0xf5fffffff003fcff 0xfebffffffe007f9f

def z786 : W := mkw 0x43700ee806f43f34 0xe86e01dd00de87e6 0xfff00ff80ffcff1e 0x9ffe01ff01ff9fe3

def z787 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0xd8167c7ffc1e9ffb 0xfb02cf8fff83d3ff

def z788 : W := mkw 0x05dd633592500004 0x00bbac66b24a0000 0xfff677b9cffc0006 0x1ffecef739ff8000

def z789 : W := mkw 0x435006a806f43f34 0xe86a00d500de87e6 0x4f9007b80ffffffe 0x09f200f701ffffff

def z790 : W := mkw 0xa0023498dc8e99ca 0xf40046931b91d339 0xd8167479fc1e9ffb 0xfb02ce8f3f83d3ff

def z791 : W := mkw 0x20003018900c8108 0x2400060312019021 0x88167079f01c8319 0x7102ce0f3e039063

def z792 : W := mkw 0x015350000b5bc007 0x002a6a00016b7800 0xba79f0000fffe006 0x774f3e0001fffc00

def z793 : W := mkw 0x008e1000090b8003 0x0011c20001217000 0xfbfff0000fffe006 0x7f7ffe0001fffc00

def z794 : W := mkw 0xa00214884d8f99cb 0xf400429109b1f339 0x020000000f9f1ce6 0x0040000001f3e39c

def z795 : W := mkw 0x05fd6b7590000000 0x00bfad6eb2000000 0x45967ff9c0000000 0x88b2cfff38000000

def z796 : W := mkw 0x01df52200b5bc007 0x003bea44016b7800 0xfffff7b80fffe006 0x7ffffef701fffc00

def z797 : W := mkw 0x4000800220202630 0x08001000440404c6 0xb86980063063ffff 0x770d3000c60c7fff

def z798 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0x48167479fc1e939b 0x8902ce8f3f83d273

def z799 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0xcbf7f0000fffe006 0x597efe0001fffc00

def z800 : W := mkw 0x0150022002500004 0x002a0044004a0000 0xfff007b80ffc0006 0x1ffe00f701ff8000

def z801 : W := mkw 0x01fd4b6500000000 0x003fa96ca0000000 0xf5ffffffc0000001 0xfebffffff8000000

def z802 : W := mkw 0xa08e3115d90b80cb 0x1411c622bb217019 0xb80e7847f0039fff 0xf701cf08fe0073ff

def z803 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0x678e0f87cf831ce6 0x0cf1c1f0f9f0639c

def z804 : W := mkw 0x035006a806d41904 0xe06a00d500da8320 0x579007b80f9c1002 0x8af200f701f38200

def z805 : W := mkw 0x048de117b0000000 0x0091bc22f6000000 0xf59ffffff0000001 0xfeb3fffffe000000

def z806 : W := mkw 0xa20214884ede998e 0xf440429109dbd331 0x020000000f9c0000 0x0040000001f38000

def z807 : W := mkw 0xa0003418d40c9188 0xb40006831a819231 0xd8167479f01c9399 0xfb02ce8f3e039273

def z808 : W := mkw 0x45fdeb77b0202630 0x08bfbd6ef60404c6 0xf5fffffff0000319 0xfebffffffe000063

def z809 : W := mkw 0x01df51050b5bc007 0x003bea20a16b7800 0xfbfff007cfffe007 0x7f7ffe00f9fffc00

def z810 : W := mkw 0x03700ee806d41904 0xe06e01dd00da8320 0xf7f00ff80f9c1c06 0x9efe01ff01f38380

def z811 : W := mkw 0x808e158d4d8f99c3 0xf011c2b1a9b1f338 0xff9e7fffcf9f9fe7 0xfff3cffff9f3f3fc

def z812 : W := mkw 0xa20214884fffdf8f 0xf440429109fffbf1 0x0a0000000fffff9e 0x0140000001fffff3

def z813 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0xcff00ff80ffc1f00 0x99fe01ff01ff83e0

def z814 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0xfdfffffff0028003 0xffbffffffe005000

def z815 : W := mkw 0xa0023498dd8f99cb 0xf40046931bb1f339 0xfa1e7c7fff9f9fff 0xff43cf8ffff3f3ff

def z816 : W := mkw 0x4020884220202630 0x08041108440404c6 0xfde98fc63063ffff 0xffbd31f8c60c7fff

def z817 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0x459ffffff0000001 0xe8b3fffffe000000

def z818 : W := mkw 0x0422bb77bb5bc007 0x0084576ef76b7800 0x0e000fffffffe007 0x81c001fffffffc00

def z819 : W := mkw 0x035006a806d41904 0xe06a00d500da8320 0xfff007f80ffc1306 0x9ffe00ff01ff8260

def z820 : W := mkw 0x4420ab77b0202630 0x0884156ef60404c6 0xdc167ffff0029ffb 0xfb82cffffe0053ff

def z821 : W := mkw 0x008c058504801800 0xc01180b0a0900300 0x778e0f87cf831ce7 0xaef1c1f0f9f0639c

def z822 : W := mkw 0x04adeb77b0000000 0x0095bd6ef6000000 0x758ffffff0000001 0xeeb1fffffe000000

def z823 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0x47900fb80f9c0c00 0x08f201f701f38180

def z824 : W := mkw 0x45fdeb77b0202630 0x08bfbd6ef60404c6 0xfdfffffff0029ffb 0xffbffffffe0053ff

def z825 : W := mkw 0x4020884220202630 0x08041108440404c6 0x206988463063fffd 0xe40d3108c60c7fff

def z826 : W := mkw 0x05fdeb77b3514005 0x00bfbd6ef66a2800 0xf7fffffff3800001 0xfefffffffe700000

def z827 : W := mkw 0x0150022002500004 0x002a0044004a0000 0x479007b80f9c0000 0x08f200f701f38000

def z828 : W := mkw 0x035006a806d41904 0xe06a00d500da8320 0x779007b80f9c0006 0x0ef200f701f38000

def z829 : W := mkw 0x0000000000000000 0x0000000000000000 0xb86988463063ffff 0xf70d3108c60c7fff

def z830 : W := mkw 0x808f55854d8bd8c3 0xd011eab0a9b17b18 0xffefff87cfe3fce7 0xfffdfff0f9fc7f9c

def z831 : W := mkw 0x01fc2b7590000000 0x003f856eb2000000 0xf5fe7ffff0000001 0xfebfcffffe000000

def z832 : W := mkw 0x000210000b5bc007 0x00004200016b7800 0xfa7ff0000fffe006 0x7f4ffe0001fffc00

def z833 : W := mkw 0x808e15854d8b98c3 0xd011c2b0a9b17318 0xffffff87cffffce7 0xfffffff0f9ffff9c

def z834 : W := mkw 0x4020884220202630 0x08041108440404c6 0x286988063063ffff 0x650d3100c60c7fff

def z835 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0xc8167479fc1e939a 0x5902ce8f3f83d273

def z836 : W := mkw 0x035006a806f41f04 0xe06a00d500de83e0 0x4f9007b80ffc0300 0x09f200f701ff8060

def z837 : W := mkw 0x45fdeb77b0202630 0x08bfbd6ef60404c6 0xfdfffffff062f39b 0xffbffffffe0c5e73

def z838 : W := mkw 0x0400233590000000 0x00800466b2000000 0xd41677f9f0000001 0xfa82ceff3e000000

def z839 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0xffffff800fffe006 0xfffffff001fffc00

def z840 : W := mkw 0x80000585448018c0 0xd00000b0a8900318 0x27800f87c3801ce5 0x84f001f0f870039c

def z841 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0xf3fff0000ffd6004 0x7e7ffe0001ffac00

def z842 : W := mkw 0x43700ee806f43f34 0xe86e01dd00de87e6 0xfff00ff80ffd7f66 0x9ffe01ff01ffafec

def z843 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0xeff00ff80ffc0f04 0x1dfe01ff01ff81e0

def z844 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0xfff00ff83ffc9f1e 0xdffe01ff07ff93e3

def z845 : W := mkw 0x0150223090000000 0x002a044612000000 0x459677b9c0000000 0x08b2cef738000000

def z846 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0x847ffffff0000001 0xf08ffffffe000000

def z847 : W := mkw 0x800205854c8218c2 0xd00040b0a9904318 0x77860f87cf821ce7 0xaef0c1f0f9f0439c

def z848 : W := mkw 0x83700ee846f41fc4 0xf06e01dd08de83f8 0xfff00ff80ffc1fe6 0x9ffe01ff01ff83fc

def z849 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0xfff18ff80ffcff06 0xdffe31ff01ff9fe0

def z850 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0x50167479fc1e139b 0xaa02ce8f3f83c273

def z851 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0x6bfff0000fffe006 0x0d7ffe0001fffc00

def z852 : W := mkw 0x45fdeb77b0202630 0x08bfbd6ef60404c6 0x65ffffbfc0616c64 0x0cbffff7f80c2d8c

def z853 : W := mkw 0xe022bc5afc2eb7ba 0xbc04578b5f85d6f7 0x607ffc3fcc7d6c64 0x0c0fff87f98fad8c

def z854 : W := mkw 0x01700ee006d01804 0xc02e01dc00da0300 0xfff00ff80ffc1c06 0x9ffe01ff01ff8380

def z855 : W := mkw 0xa1df50004b5bc08f 0x143bea00096b7811 0xfbfff0000fffe09e 0x7f7ffe0001fffc13

def z856 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0xfff98ff80ffc1f06 0xffff31ff01ff83e0

def z857 : W := mkw 0x03714ee806f41f04 0xe06e29dd00de83e0 0xfff1fff80ffc1f06 0xdffe3fff01ff83e0

def z858 : W := mkw 0x05dd633590000000 0x00bbac66b2000000 0x45967fbfc0000001 0x88b2cff7f8000000

def z859 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0xfff98ff83fffff9f 0xffff31ff07fffff3

def z860 : W := mkw 0x43708eea26f43f34 0xe86e11dd44de87e6 0x67f98fbe0ffd6c64 0x0cff31f7c1ffad8c

def z861 : W := mkw 0x05dd633590000000 0x00bbac66b2000000 0x759e7fbfc0031ce7 0xaeb3cff7f800639c

def z862 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0xfdfffffff0039fff 0xffbffffffe0073ff

def z863 : W := mkw 0x208c319d918d8949 0x64118633b231b129 0xaf987bfe339d8f7c 0x55f30f7fc673b1ef

def z864 : W := mkw 0x04aff957b90bc003 0x0095ff2af7217800 0xb86ff847f063e007 0xf70dff08fe0c7c00

def z865 : W := mkw 0xa00214884d8f99cb 0xf400429109b1f339 0x020000000f9c0000 0x0040000001f38000

def z866 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0x45f7f7b9c0000000 0x08befef738000000

def z867 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0x77860f87cf801ce7 0x8ef0c1f0f9f0039c

def z868 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0x678e0f87cf830ce5 0x2cf1c1f0f9f0619c

def z869 : W := mkw 0x0420ab77b0000000 0x0084156ef6000000 0x04067ffff0000001 0xe080cffffe000000

def z870 : W := mkw 0x45fdeb77b0202630 0x08bfbd6ef60404c6 0xf5fffffff003fff9 0xfebffffffe007fff

def z871 : W := mkw 0x05fd6b7590000000 0x00bfad6eb2000000 0xf5fffff9c0000000 0xfebfffff38000000

def z872 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0xfff80ffe0ffd1f66 0x9fff01ffc1ffa3ec

def z873 : W := mkw 0x808e058d4d8719c3 0xf011c0b1a9b0e338 0xff9e0fffff9f9fff 0xfff3c1fffff3f3ff

def z874 : W := mkw 0xe2229cca6efebfbe 0xfc4453994ddfd7f7 0xba6988463fffffff 0xf74d3108c7ffffff

def z875 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0x778e0f87cf801ce1 0xaef1c1f0f9f0039c

def z876 : W := mkw 0x41ffd8422b7be637 0x083ffb08456f7cc6 0x439678463f9c1ff9 0x8872cf08c7f383ff

def z877 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0x2beff0000fffe006 0x657dfe0001fffc00

def z878 : W := mkw 0xa3723af0dafa8e8e 0x546e475e1b5f51d1 0x27e67b81f3e28c9d 0x64fccf703e7c5193

def z879 : W := mkw 0x808e15854d8b98c3 0xd011c2b0a9b17318 0x778e7f87cf839ce7 0xeef1cff0f9f0739c

def z880 : W := mkw 0x02200ee804a41f00 0xe04401dd009483e0 0xff900ff80f9c1f06 0x9ff201ff01f383e0

def z881 : W := mkw 0x068de59fb6f41f04 0xe0d1bcb3f6de83e0 0x0a0ff007fffc1f07 0x6141fe00ffff83e0

def z882 : W := mkw 0x02200ee806f41f04 0xe04401dd00de83e0 0x7f800ff80ffc1f06 0x8ff001ff01ff83e0

def z883 : W := mkw 0xe220aefaf4a43fb8 0xfc4415df5e9487f7 0x04000ffff0001ff9 0x808001fffe0003ff

def z884 : W := mkw 0x035006a806d41904 0xe06a00d500da8320 0x47900fb80f9c1c00 0x88f201f701f38380

def z885 : W := mkw 0x808e0185498308c3 0x5011c030a9306118 0x278e0b87c3810c64 0x04f1c170f870218c

def z886 : W := mkw 0xa20214884ede998e 0xf440429109dbd331 0x0a0000000f9e939a 0x0140000001f3d273

def z887 : W := mkw 0x83fe0b6d4b7707c7 0x307fc16da96ee0f8 0x887e007fc07f03e1 0x310fc00ff80fe07c

def z888 : W := mkw 0x008c211590000000 0x00118422b2000000 0x459677b9c0000000 0x08b2cef738000000

def z889 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0x4f900ff80ffc1f06 0x89f201ff01ff83e0

def z890 : W := mkw 0x0420ab77b0000000 0x0084156ef6000000 0xf47ffffff0000001 0xfe8ffffffe000000

def z891 : W := mkw 0x008c211590000000 0x00118422b2000000 0xfd9e7ffff0039fff 0xffb3cffffe0073ff

def z892 : W := mkw 0x43700ee806f43f34 0xe86e01dd00de87e6 0xfff00ff83fffffff 0xfffe01ff07ffffff

def z893 : W := mkw 0x45fdeb77b0202630 0x08bfbd6ef60404c6 0xfdfffffff061ef7d 0xffbffffffe0c3def

def z894 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0xc8167479fc1c9399 0xd902ce8f3f839273

def z895 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0xfff00ff80fff1fe6 0x9ffe01ff01ffe3fc

def z896 : W := mkw 0x0000241894041100 0xa000048312808220 0xd8167479fc1e939b 0xfb02ce8f3f83d273

def z897 : W := mkw 0x808c0585448018c0 0xd01180b0a8900318 0x778e0f87cf801ce7 0xaef1c1f0f9f0039c

def z898 : W := mkw 0x4020884220202630 0x08041108440404c6 0x886980463063ffff 0x710d3008c60c7fff

def z899 : W := mkw 0x05dd633590000000 0x00bbac66b2000000 0x75967fb9c0000000 0x8eb2cff738000000

def z900 : W := mkw 0xa00214884fdfd9cf 0xf400429109fbfb39 0x0a0000000ffffffe 0x0140000001ffffff

def z901 : W := mkw 0x015350000a5ac006 0x002a6a00014b5800 0xfbf7f0000ffee006 0x7f7efe0001ffdc00

def z902 : W := mkw 0x45fdeb77b0202630 0x08bfbd6ef60404c6 0xcdf7f7f9f060e318 0x59befeff3e0c1c63

def z903 : W := mkw 0x035006a806d41904 0xe06a00d500da8320 0x67900fb80f9c0c04 0x0cf201f701f38180

def z904 : W := mkw 0x05fdeb77b2500004 0x00bfbd6ef64a0000 0xf7ffffffff9c0001 0xfefffffffff38000

def z905 : W := mkw 0x43708eea26f43f34 0xe86e11dd44de87e6 0xfff98ffe0fffff66 0xffff31ffc1ffffec

def z906 : W := mkw 0x43708eea26f43f34 0xe86e11dd44de87e6 0xcff187f83ffce318 0x59fe30ff07ff9c63

def z907 : W := mkw 0x45fdeb77b0002030 0x08bfbd6ef6000406 0xfdfffffff003f3fb 0xffbffffffe007e7f

def z908 : W := mkw 0x035006a806f41f04 0xe06a00d500de83e0 0x479007b80ffc0c04 0x08f200f701ff8180

def z909 : W := mkw 0x43708eea26f43f34 0xe86e11dd44de87e6 0xfff18ff80ffc7f06 0x9ffe31ff01ff8fe0

def z910 : W := mkw 0x05dd633590000000 0x00bbac66b2000000 0x659e7fbfc0000000 0x0cb3cff7f8000000

def z911 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0xf7ffffffff800007 0xfefffffffff00000

def z912 : W := mkw 0x808f45854d8318c3 0xd011e8b0a9b06318 0x778fff87cf831ce7 0xeef1fff0f9f0639c

def z913 : W := mkw 0x808e15854d8bd8c3 0xd011c2b0a9b17b18 0x778e0f87cf83fce7 0xaef1c1f0f9f07f9c

def z914 : W := mkw 0x0570ab77b0000000 0x00ae156ef6000000 0xf5f67ffff0000001 0xfebecffffe000000

def z915 : W := mkw 0x41708a6222702634 0x082e114c444e04c6 0xfff98ffe3fffffff 0xffff31ffc7ffffff

def z916 : W := mkw 0x05dde337b0000000 0x00bbbc66f6000000 0x759fffbff0000001 0xeeb3fff7fe000000

def z917 : W := mkw 0x05fdeb77b1010001 0x00bfbd6ef6202000 0xf7fffffff3810005 0xfefffffffe702000

def z918 : W := mkw 0x4620afffb4a43f30 0xe8c415fff69487e6 0x04000ffff0001ff9 0x808001fffe0003ff

def z919 : W := mkw 0x048f7115990bc003 0x0091ee22b3217800 0x000ff001c003e000 0x6001fe0038007c00

def z920 : W := mkw 0x015150000258c004 0x002a2a00004b1800 0xfbf9f0000fffe006 0x7f7f3e0001fffc00

def z921 : W := mkw 0x05fdeb77b1014001 0x00bfbd6ef6202800 0xf5fffffff0016001 0xfebffffffe002c00

def z922 : W := mkw 0x05dd633590000000 0x00bbac66b2000000 0xd59677b9c0000000 0x7ab2cef738000000

def z923 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0x759e7ffff0000001 0xaeb3cffffe000000

def z924 : W := mkw 0x05fdeb77b2700604 0x00bfbd6ef64e00c0 0xfffffffffffc1f07 0xffffffffffff83e0

def z925 : W := mkw 0xa2221cc84efe9f8e 0xf444439909dfd3f1 0xba6008403ffe9f9f 0xf74c010807ffd3f3

def z926 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0x57860f87cf821ce3 0xaaf0c1f0f9f0439c

def z927 : W := mkw 0x808c0585458118c1 0xd01180b0a8b02318 0x27880f87c3810c64 0x04f101f0f870218c

def z928 : W := mkw 0x015210000a5a8006 0x002a4200014b5000 0xfbfff0000fffe006 0x7f7ffe0001fffc00

def z929 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0xf5f7fff9f0000000 0xdebeffff3e000000

def z930 : W := mkw 0xa0023018d80e818a 0x340046031b01d031 0xd8167079fc1e839b 0x7b02ce0f3f83d073

def z931 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0xd0167479fc1c1399 0xfa02ce8f3f838273

def z932 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0xfdfffffff060e001 0xffbffffffe0c1c00

def z933 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0x8a7ff0000fffe006 0x714ffe0001fffc00

def z934 : W := mkw 0xa0023418dd0f91cb 0xb40046831ba1f239 0xd8167479fc1f93fb 0xfb02ce8f3f83f27f

def z935 : W := mkw 0x05dde337b0000000 0x00bbbc66f6000000 0x459ff7bfc0000000 0x08b3fef7f8000000

def z936 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0x778e0f87cf830c66 0x2ef1c1f0f9f0618c

def z937 : W := mkw 0xa0023498dd8f99cb 0xf40046931bb1f339 0xff967ff9ff9f9fff 0xfff2cfff3ff3f3ff

def z938 : W := mkw 0x00200cc804a41f00 0xe0040199009483e0 0xfff00ff80ffc1f06 0x9ffe01ff01ff83e0

def z939 : W := mkw 0x05fd6b7590200600 0x00bfad6eb20400c0 0xfdf67ff9c0601f06 0x9fbecfff380c03e0

def z940 : W := mkw 0x04adeb77b0000000 0x0095bd6ef6000000 0x04067ffff0000001 0x8080cffffe000000

def z941 : W := mkw 0x43708eea26f43f34 0xe86e11dd44de87e6 0xfff00ffe3fffffff 0x9ffe01ffc7ffffff

def z942 : W := mkw 0x83700ee846f41f84 0xf06e01dd08de83f0 0xfff00ff9cffc1f87 0x9ffe01ff39ff83f0

def z943 : W := mkw 0x05dd633590000000 0x00bbac66b2000000 0xfdfff7b9c063e006 0x7fbffef7380c7c00

def z944 : W := mkw 0x45fdeb77b0202630 0x08bfbd6ef60404c6 0xfdfffffff0601fff 0xffbffffffe0c03ff

def z945 : W := mkw 0x808f45854d8358c3 0xd011e8b0a9b06b18 0x778f8f87cf837ce7 0xaef1f1f0f9f06f9c

def z946 : W := mkw 0xa0023498dc8e998a 0xf40046931b91d331 0xda167479ff9e9f9f 0xfb42ce8f3ff3d3f3

def z947 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0xaff00bf80ffc1f06 0x15fe017f01ff83e0

def z948 : W := mkw 0xa48ff117f90b80cb 0x1491fe22ff217019 0x000ff007f00380f9 0x6001fe00fe00701f

def z949 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0xffee0f87cfe31ce7 0xbffdc1f0f9fc639c

def z950 : W := mkw 0x4020884220202630 0x08041108440404c6 0xf87988463c7fffff 0xff0f3108c78fffff

def z951 : W := mkw 0x05dd633590000000 0x00bbac66b2000000 0xdd9677f9f002939b 0xfbb2ceff3e005273

def z952 : W := mkw 0x03714ee806f45f04 0xe06e29dd00de8be0 0xfff18ff80ffc7f06 0x9ffe31ff01ff8fe0

def z953 : W := mkw 0x05dd633590000000 0x00bbac66b2000000 0x459677b9f0000001 0x68b2cef73e000000

def z954 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0xf81e7479fc1f939f 0xff03ce8f3f83f273

def z955 : W := mkw 0x43708eea26f43f34 0xe86e11dd44de87e6 0xfff18ff83ffeff9f 0xfffe31ff07ffdff3

def z956 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0xfbfff8060fffe007 0xff7fff00c1fffc00

def z957 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0x278e0b87cf831ce7 0x24f1c170f9f0639c

def z958 : W := mkw 0x035006a806f41f04 0xe06a00d500de83e0 0x7f900fb80ffc1f06 0x8ff201f701ff83e0

def z959 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0xfff00ff80fffff06 0x9ffe01ff01ffffe0

def z960 : W := mkw 0x035006a806d41904 0xe06a00d500da8320 0xfff987b80fffe006 0x7fff30f701fffc00

def z961 : W := mkw 0x035006a806d41904 0xe06a00d500da8320 0x4f9007b80ffc0006 0x09f200f701ff8000

def z962 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0xff8e0f87cf839ce7 0xfff1c1f0f9f0739c

def z963 : W := mkw 0xa08e15854d8b98cb 0xd411c2b0a9b17319 0x778e0f87cf839cff 0xaef1c1f0f9f0739f

def z964 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0xf87ff479fc1e939b 0xff0ffe8f3f83d273

def z965 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0xfff80ff80fff1f06 0xbfff01ff01ffe3e0

def z966 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0xf5ffffbfc0000000 0x7ebffff7f8000000

def z967 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0xfff00fb80ffc0c06 0x1ffe01f701ff8180

def z968 : W := mkw 0x0420ab77b0000000 0x0084156ef6000000 0x44167ffff0000001 0x8882cffffe000000

def z969 : W := mkw 0x45fdeb77b2702634 0x08bfbd6ef64e04c6 0xffffffffffffffff 0xffffffffffffffff

def z970 : W := mkw 0x808e15854d8b98c3 0xd011c2b0a9b17318 0x7f8e0f87cf9f9ce7 0xaff1c1f0f9f3f39c

def z971 : W := mkw 0x048ff117b90bc003 0x0091fe22f7217800 0x000ff007f0000001 0x6001fe00fe000000

def z972 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0xf5f67ffff0000001 0x9ebecffffe000000

def z973 : W := mkw 0x03700ee806d41904 0xe06e01dd00da8320 0x47900ff80f9c0000 0x88f201ff01f38000

def z974 : W := mkw 0x45fdeb77b0202630 0x08bfbd6ef60404c6 0xf5fffffff0617ffd 0xfebffffffe0c2fff

def z975 : W := mkw 0x05fd6b7590000000 0x00bfad6eb2000000 0x65f67fb9c0000000 0x0cbecff738000000

def z976 : W := mkw 0xa00214884d8f99cb 0xf400429109b1f339 0x0a0000000f9e939a 0x0140000001f3d273

def z977 : W := mkw 0x0000211590000000 0x00000422b2000000 0xd4167ffff0000001 0xfa82cffffe000000

def z978 : W := mkw 0x81df50004b5bc0c7 0x103bea00096b7818 0xfbfff0000fffe0e6 0x7f7ffe0001fffc1c

def z979 : W := mkw 0xa0023018d80e818a 0x340046031b01d031 0x88167079f01c8318 0x5102ce0f3e039063

def z980 : W := mkw 0x05dd633590000000 0x00bbac66b2000000 0x559677b9c0000001 0xaab2cef738000000

def z981 : W := mkw 0x4020884220202630 0x08041108440404c6 0xf8798c7e3063ffff 0xff0f318fc60c7fff

def z982 : W := mkw 0x04acab77b0000000 0x0095956ef6000000 0xf59e7ffff0000001 0xfeb3cffffe000000

def z983 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0xfbfff401cfffe007 0xff7ffe8039fffc00

def z984 : W := mkw 0x45fdeb77b0202630 0x08bfbd6ef60404c6 0xf5fffffff063ecfd 0xfebffffffe0c7d9f

def z985 : W := mkw 0x43708eea26f43f34 0xe86e11dd44de87e6 0xfff00ffe0ffc1f66 0x9ffe01ffc1ff83ec

def z986 : W := mkw 0x43708eea26f43f34 0xe86e11dd44de87e6 0xfff98ffe3ffd7fff 0x9fff31ffc7ffafff

def z987 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0xfff00ff80ffc0300 0x9ffe01ff01ff8060

def z988 : W := mkw 0x44aff957b92be633 0x0895ff2af7257cc6 0xb86ff847f063ffff 0xf70dff08fe0c7fff

def z989 : W := mkw 0x008e018509830843 0x4011c030a1306108 0x778e0f87cf830c67 0xaef1c1f0f9f0618c

def z990 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0xfbfff4780fffe006 0xff7ffe8f01fffc00

def z991 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0x65ffffbff0000001 0x6cbffff7fe000000

def z992 : W := mkw 0x05dd633590000000 0x00bbac66b2000000 0x459e77bfc0000001 0x28b3cef7f8000000

def z993 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0xc8167479fc1e8399 0x7902ce8f3f83d073

def z994 : W := mkw 0x80000585448018c0 0xd00000b0a8900318 0x77880f87cf831ce7 0xaef101f0f9f0639c

def z995 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0xfdfffffff063f39f 0xffbffffffe0c7e73

def z996 : W := mkw 0x0170aa72b0000000 0x002e154e56000000 0xf5fffffff0000001 0xfebffffffe000000

def z997 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0xfbfff0000ffce000 0x7f7ffe0001ff9c00

def z998 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0x778e0fc7ff831fff 0xaef1c1f8fff063ff

def z999 : W := mkw 0x43708eea26f43f34 0xe86e11dd44de87e6 0xfff18ff83ffffffe 0xdffe31ff07ffffff

def z1000 : W := mkw 0x01dd400002500004 0x003ba800004a0000 0xfbfff0000fffe006 0x7f7ffe0001fffc00

def z1001 : W := mkw 0xa08e158d4d8f99cb 0xf411c2b1a9b1f339 0x778e0f87cf9f1ce7 0xaef1c1f0f9f3e39c

def z1002 : W := mkw 0x45fdeb77b0202630 0x08bfbd6ef60404c6 0x45967ffff0001ff9 0x88b2cffffe0003ff

def z1003 : W := mkw 0x00202a7090000000 0x0004054e12000000 0xd4167ff9f0000001 0xfa82cfff3e000000

def z1004 : W := mkw 0x05dd633590000000 0x00bbac66b2000000 0xf5fff7f9f0000001 0xfebffeff3e000000

def z1005 : W := mkw 0x43708eea26f43f34 0xe86e11dd44de87e6 0xfff80ffe3fff1fff 0xbfff01ffc7ffe3ff

def z1006 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0xf79e7f87cf831ce7 0xfef3cff0f9f0639c

def z1007 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0xd5f7f7f9f0000001 0xfabefeff3e000000

def z1008 : W := mkw 0x01dd50000258c004 0x003baa00004b1800 0xfbfff0000ffce006 0x7f7ffe0001ff9c00

def z1009 : W := mkw 0x8151558546d8d8c4 0xd02a2ab0a8db1b18 0x8c71ff87c07cfce1 0xd18e3ff0f80f9f9c

def z1010 : W := mkw 0x81df51054b5bc0c7 0x103bea20a96b7818 0xfbfff001cfffe006 0x7f7ffe0039fffc00

def z1011 : W := mkw 0xa00214884d8f99cb 0xf400429109b1f339 0xba0808463f9f9fff 0xf7410108c7f3f3ff

def z1012 : W := mkw 0x035006a806d41904 0xe06a00d500da8320 0xfff00fb80ffc1c06 0x9ffe01f701ff8380

def z1013 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0xd8167479fc1c931a 0xdb02ce8f3f839263

def z1014 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0xfbfff0003fffe09f 0x7f7ffe0007fffc13

def z1015 : W := mkw 0xa0023498dc8e998a 0xf40046931b91d331 0xdc167ff9fc1e9f9b 0xfb82cfff3f83d3f3

def z1016 : W := mkw 0x03700a6802740704 0x206e014d004e80e0 0xfff00ff80ffc0306 0x9ffe01ff01ff8060

def z1017 : W := mkw 0x43708eea26f43f34 0xe86e11dd44de87e6 0xfff18ffe3ffcffff 0xdffe31ffc7ff9fff

def z1018 : W := mkw 0x45fdeb77b0202630 0x08bfbd6ef60404c6 0xf5fffffff0031fff 0xfebffffffe0063ff

def z1019 : W := mkw 0x035006a806f41f04 0xe06a00d500de83e0 0xdf9007f80ffc1f06 0x9bf200ff01ff83e0

def z1020 : W := mkw 0x808e15854d8b98c3 0xd011c2b0a9b17318 0x779e7f87cf9f1ce7 0xaef3cff0f9f3e39c

def z1021 : W := mkw 0x035006a806d41904 0xe06a00d500da8320 0xdf9007b80f9c0002 0x1bf200f701f38000

def z1022 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0xc5f7fffff0000001 0xd8befffffe000000

def z1023 : W := mkw 0xe020addff4a43ff8 0xfc0415bbfe9487ff 0x04000ffff0001ff9 0x808001fffe0003ff

def z1024 : W := mkw 0x45fdeb77b0202630 0x08bfbd6ef60404c6 0xfdfffffff060ff1f 0xffbffffffe0c1fe3

def z1025 : W := mkw 0x05dd633590000000 0x00bbac66b2000000 0xc59677f9f0000000 0x58b2ceff3e000000

def z1026 : W := mkw 0xa3700ee846f41f8c 0xf46e01dd08de83f1 0xfff00ff80ffc1f9e 0x9ffe01ff01ff83f3

def z1027 : W := mkw 0x05dd633593514005 0x00bbac66b26a2800 0x479677b9c3800000 0x08f2cef738700000

def z1028 : W := mkw 0x015350000b5bc007 0x002a6a00016b7800 0xfbf1f0000fffe006 0x5f7e3e0001fffc00

def z1029 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0xfbfff0000ffd6006 0x1f7ffe0001ffac00

def z1030 : W := mkw 0x008c211590000000 0x00118422b2000000 0x759e7fbfc0000001 0xaeb3cff7f8000000

def z1031 : W := mkw 0x01fd6a7090000000 0x003fad4e12000000 0xf5fffff9f0000001 0xfebfffff3e000000

def z1032 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0x75ffffbfc0000001 0xaebffff7f8000000

def z1033 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0x25effffff0000001 0xe4bdfffffe000000

def z1034 : W := mkw 0x05dd633590000000 0x00bbac66b2000000 0x759e77b9c0000000 0x2eb3cef738000000

def z1035 : W := mkw 0x808e058d4d8719c3 0xf011c0b1a9b0e338 0x7f8e0f87cf9f1fe7 0xaff1c1f0f9f3e3fc

def z1036 : W := mkw 0x035006a806d41904 0xe06a00d500da8320 0xcf9007f80f9c0300 0x19f200ff01f38060

def z1037 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0x2fe00ff80ffc1f06 0x85fc01ff01ff83e0

def z1038 : W := mkw 0xa0023498dc8e998a 0xf40046931b91d331 0xdf9677f9ff9e939b 0xfbf2ceff3ff3d273

def z1039 : W := mkw 0x43708eea26f43f34 0xe86e11dd44de87e6 0xfff00ffe3ffe9fff 0xfffe01ffc7ffd3ff

def z1040 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0x47f007b80ffc0000 0x08fe00f701ff8000

def z1041 : W := mkw 0x01df51050b5bc007 0x003bea20a16b7800 0xfffff781cfffe006 0x7ffffef039fffc00

def z1042 : W := mkw 0x0571ea72b0000000 0x00ae3d4e56000000 0xf5f7fff9f0000001 0xfebeffff3e000000

def z1043 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0xfbfff0000ffff087 0xff7ffe0001fffe10

def z1044 : W := mkw 0xe08eb117f90ba0fb 0x1c11d622ff21741f 0x000ff007f003e0f9 0x6001fe00fe007c1f

def z1045 : W := mkw 0x048d633590000000 0x0091ac66b2000000 0x040677b9c0000000 0x0080cef738000000

def z1046 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0x45967fbfc0000000 0x08b2cff7f8000000

def z1047 : W := mkw 0x035006a806d41904 0xe06a00d500da8320 0x77900fb80f9c0000 0x8ef201f701f38000

def z1048 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0xfff67ff80ffc1f06 0xfffecfff01ff83e0

def z1049 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0x47860f87cf800c60 0x08f0c1f0f9f0018c

def z1050 : W := mkw 0x808e0185498308c3 0x5011c030a9306118 0x778e0f87c3830ce5 0xaef1c1f0f870619c

def z1051 : W := mkw 0x808c0585458118c1 0xd01180b0a8b02318 0x07800f87c3801ce1 0x80f001f0f870039c

def z1052 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0xf8767479fc7e939f 0xff0ece8f3f8fd273

def z1053 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0x88167079fc1e939b 0x7102ce0f3f83d273

def z1054 : W := mkw 0xa0023418dd0fd18b 0xb40046831ba1fa31 0xd8167479fc1ff39b 0xfb02ce8f3f83fe73

def z1055 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0x678e0f87cf811ce5 0x8cf1c1f0f9f0239c

def z1056 : W := mkw 0xa08e158d4d8f99cb 0xf411c2b1a9b1f339 0xff9e0fffcf9f9fff 0xbff3c1fff9f3f3ff

def z1057 : W := mkw 0xe20214884efebfbe 0xfc40429109dfd7f7 0x0a0000000ffffffe 0x0140000001ffffff

def z1058 : W := mkw 0x008c018501810841 0x40118030a0302108 0x778e0f87c3831ce7 0xaef1c1f0f870639c

def z1059 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0xf7f00ff80ffc0c04 0x9efe01ff01ff8180

def z1060 : W := mkw 0xa20214884cae9f8a 0xf44042910995d3f1 0x080000000c1e9f9a 0x010000000183d3f3

def z1061 : W := mkw 0x05dd633590000000 0x00bbac66b2000000 0xd59677f9c0000000 0x9ab2ceff38000000

def z1062 : W := mkw 0xa0023418dd0f918b 0xb40046831ba1f231 0xda167479ff9f939f 0xfb42ce8f3ff3f273

def z1063 : W := mkw 0x048de337b0000000 0x0091bc66f6000000 0x040ff7bff0000001 0x6081fef7fe000000

def z1064 : W := mkw 0x45fdeb77b0202630 0x08bfbd6ef60404c6 0xfdfffffff0617f67 0xffbffffffe0c2fec

def z1065 : W := mkw 0x01700e6806541104 0xa02e01cd00ca8220 0xfff00ff80ffc1306 0x9ffe01ff01ff8260

def z1066 : W := mkw 0x45fdeb77b3716635 0x08bfbd6ef66e2cc6 0xf7fffffff3e16c65 0xfefffffffe7c2d8c

def z1067 : W := mkw 0x03700ae002f00e04 0x406e015c005e01c0 0xfff00ff80ffc0c06 0x9ffe01ff01ff8180

def z1068 : W := mkw 0xa20214884efe9f8e 0xf440429109dfd3f1 0x0a0000000ffc1f06 0x0140000001ff83e0

def z1069 : W := mkw 0x035006a806f41f04 0xe06a00d500de83e0 0x479007b80f9c1f00 0x08f200f701f383e0

def z1070 : W := mkw 0xa48ff117f90bc08b 0x1491fe22ff217811 0x000ff007f003e099 0x6001fe00fe007c13

def z1071 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0xe5fffffff0000000 0x5cbffffffe000000

def z1072 : W := mkw 0x45fdeb77b0202630 0x08bfbd6ef60404c6 0xfdfffffff063ec67 0xffbffffffe0c7d8c

def z1073 : W := mkw 0x0771ceea26f41f04 0xe0ee39dd44de83e0 0xfff18ff80ffc1f06 0x9ffe31ff01ff83e0

def z1074 : W := mkw 0x05dd633590000000 0x00bbac66b2000000 0x459ff7b9c0000000 0x68b3fef738000000

def z1075 : W := mkw 0x05dde337b0000000 0x00bbbc66f6000000 0xd59ff7fff0000001 0xfab3fefffe000000

def z1076 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0x6ff00fb80ffc1f06 0x0dfe01f701ff83e0

def z1077 : W := mkw 0x808e0185498308c3 0x5011c030a9306118 0x378e0b87c3831ce7 0xa6f1c170f870639c

def z1078 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0xf5fffffff003e001 0xfebffffffe007c00

def z1079 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0xdf900ff80f9c1f02 0x9bf201ff01f383e0

def z1080 : W := mkw 0x43708eea26f43f34 0xe86e11dd44de87e6 0xfff98ffe3ffc1fff 0xffff31ffc7ff83ff

def z1081 : W := mkw 0x05dd633590000000 0x00bbac66b2000000 0xf5f677b9c0000000 0x1ebecef738000000

def z1082 : W := mkw 0x05dd633590000000 0x00bbac66b2000000 0x459677f9f0000001 0x88b2ceff3e000000

def z1083 : W := mkw 0x45fdeb77b0202630 0x08bfbd6ef60404c6 0xfdfffffff063e3f9 0xffbffffffe0c7c7f

def z1084 : W := mkw 0x808e058d4d8719c3 0xf011c0b1a9b0e338 0x778e0fffcf831fe7 0xaef1c1fff9f063fc

def z1085 : W := mkw 0xa08e158d4d8f99cb 0xf411c2b1a9b1f339 0xff9e7f87cf9f9fff 0xfff3cff0f9f3f3ff

def z1086 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0xfff98ff80ffd7f06 0x9fff31ff01ffafe0

def z1087 : W := mkw 0xa08e3115d90b80cb 0x1411c622bb217019 0x00067001f0028099 0x6000ce003e005013

def z1088 : W := mkw 0x05dd633592500004 0x00bbac66b24a0000 0x479677b9cf9c0000 0x08f2cef739f38000

def z1089 : W := mkw 0x015350000b5bc007 0x002a6a00016b7800 0x8a71f0000ffce000 0x514e3e0001ff9c00

def z1090 : W := mkw 0x43700ee806f43f34 0xe86e01dd00de87e6 0xfff80ffe0fffffff 0xbfff01ffc1ffffff

def z1091 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0xf5fffffff0001399 0xfebffffffe000273

def z1092 : W := mkw 0x45fdeb77b0202630 0x08bfbd6ef60404c6 0xf5fffffff0000c61 0xfebffffffe00018c

def z1093 : W := mkw 0x4420ab77b0202630 0x0884156ef60404c6 0xfc7ffffff063ffff 0xff8ffffffe0c7fff

def z1094 : W := mkw 0x01df51050b5bc047 0x003bea20a16b7808 0xfbfff0060fffe066 0x7f7ffe00c1fffc0c

def z1095 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0xabf9f0000fffe006 0x557f3e0001fffc00

def z1096 : W := mkw 0x05fdeb77b0200600 0x00bfbd6ef60400c0 0xfdfffffff063ff07 0xffbffffffe0c7fe0

def z1097 : W := mkw 0x035006a806d41904 0xe06a00d500da8320 0x67f007b80ffc0004 0x0cfe00f701ff8000

def z1098 : W := mkw 0x05fdeb77b0200600 0x00bfbd6ef60400c0 0xf5fffffff0600c05 0xfebffffffe0c0180

def z1099 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0x43f7f0000ffc6000 0x087efe0001ff8c00

def z1100 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0xd8167479fc1c139b 0x9b02ce8f3f838273

def z1101 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0x77ef8f87cfe37ce7 0xaefdf1f0f9fc6f9c

def z1102 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0xfbfff8463fffffff 0xff7fff08c7ffffff

def z1103 : W := mkw 0x05dde337b0000000 0x00bbbc66f6000000 0xf5fff7bff0000001 0x7ebffef7fe000000

def z1104 : W := mkw 0x0000201090000000 0x0000040212000000 0xf5967ff9f0000001 0xfeb2cfff3e000000

def z1105 : W := mkw 0x45fdeb77b0202630 0x08bfbd6ef60404c6 0xf5fffffff0606001 0xfebffffffe0c0c00

def z1106 : W := mkw 0x800205854d8318c3 0xd00040b0a9b06318 0x77800f87cf831ce7 0x8ef001f0f9f0639c

def z1107 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0xd81ff479fc1ff39b 0xfb03fe8f3f83fe73

def z1108 : W := mkw 0x015150000258c004 0x002a2a00004b1800 0x8a71f0000ffce006 0x514e3e0001ff9c00

def z1109 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0xf5ffffffc0000000 0x9ebffffff8000000

def z1110 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0x47860f87cf831ce7 0x88f0c1f0f9f0639c

def z1111 : W := mkw 0xa00214884c8e998a 0xf40042910991d331 0x0a0000000f9e9f9e 0x0140000001f3d3f3

def z1112 : W := mkw 0x035006a806d41904 0xe06a00d500da8320 0xd79007f80f9c0000 0x9af200ff01f38000

def z1113 : W := mkw 0x03708eea26f41f04 0xe06e11dd44de83e0 0xfff98ffe3ffe9f9f 0xffff31ffc7ffd3f3

def z1114 : W := mkw 0x0000048804841900 0xe000009100908320 0xdf9007f80f9c1302 0x9bf200ff01f38260

def z1115 : W := mkw 0x40208cca24a43f30 0xe8041199449487e6 0xfff98ffe3fffffff 0xffff31ffc7ffffff

def z1116 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0x478e0f87cf831ce1 0xa8f1c1f0f9f0639c

def z1117 : W := mkw 0x03700ee806d41904 0xe06e01dd00da8320 0xfff00ff80ffc0006 0x9ffe01ff01ff8000

def z1118 : W := mkw 0x05fdeb77b0200600 0x00bfbd6ef60400c0 0xfdfffffff0600301 0xffbffffffe0c0060

def z1119 : W := mkw 0x4170aa72b0202630 0x082e154e560404c6 0xfdfffffff063ffff 0xffbffffffe0c7fff

def z1120 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0x778f8f87cf83fce7 0xeef1f1f0f9f07f9c

def z1121 : W := mkw 0x20023018980e810a 0x240046031301d021 0xd8167479fc1e831b 0xfb02ce8f3f83d063

def z1122 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0xd8167479fc1e831a 0x7b02ce8f3f83d063

def z1123 : W := mkw 0x20003418940c9108 0xa400068312819221 0xd8167479fc1c931b 0xfb02ce8f3f839263

def z1124 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0x778e0f87cf811c66 0x8ef1c1f0f9f0238c

def z1125 : W := mkw 0x0000048804841900 0xe000009100908320 0x479007b80f9c0000 0x08f200f701f38000

def z1126 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0xfbf7f0000ffce006 0x5f7efe0001ff9c00

def z1127 : W := mkw 0x05fd6b7590000000 0x00bfad6eb2000000 0xf5f67ff9f0000001 0xfebecfff3e000000

def z1128 : W := mkw 0xe0229cca6dafbffb 0xfc0453994db5f7ff 0xba6988463fffffff 0xf74d3108c7ffffff

def z1129 : W := mkw 0x0000048804841900 0xe000009100908320 0xff980ffe3f9f9fff 0xfff301ffc7f3f3ff

def z1130 : W := mkw 0xa0023498dc8e998a 0xf40046931b91d331 0xff9e7fffff9f9fff 0xfff3cffffff3f3ff

def z1131 : W := mkw 0x035006a806d41904 0xe06a00d500da8320 0x4f9007b80f9c1302 0x09f200f701f38260

def z1132 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0xdbf7f0000ffee002 0x7b7efe0001ffdc00

def z1133 : W := mkw 0x05dd633590000000 0x00bbac66b2000000 0xc5f7f7b9c0000000 0x58befef738000000

def z1134 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0x65fffffff0000001 0x8cbffffffe000000

def z1135 : W := mkw 0x45dde337b0002030 0x08bbbc66f6000406 0x459ff7bff003e0f9 0x68b3fef7fe007c1f

def z1136 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0xcff007f80ffc1f06 0x19fe00ff01ff83e0

def z1137 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0xfbfff0000ffff39e 0x7f7ffe0001fffe73

def z1138 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0x40167479fc1c0318 0x0802ce8f3f838063

def z1139 : W := mkw 0x01dd50000359c005 0x003baa00006b3800 0xfbf9f0000ffde006 0x5f7f3e0001ffbc00

def z1140 : W := mkw 0x05fd6b7590000000 0x00bfad6eb2000000 0xc5f677f9c0000000 0x18beceff38000000

def z1141 : W := mkw 0x47fdcbe722f02e34 0x48ffb97ce45e05c6 0x27e98b8603e16c64 0x04fd3170c07c2d8c

def z1142 : W := mkw 0x43708eea26f43f34 0xe86e11dd44de87e6 0x47900ffe3f9c1ff9 0x88f201ffc7f383ff

def z1143 : W := mkw 0xa08e3115d90b80cb 0x1411c622bb217019 0x00067001c0000000 0x0000ce0038000000

def z1144 : W := mkw 0x00aca957b0000000 0x0015952af6000000 0xf5fffffff0000001 0xfebffffffe000000

def z1145 : W := mkw 0x808c0585458118c1 0xd01180b0a8b02318 0x77880f87cf811ce7 0x8ef101f0f9f0239c

def z1146 : W := mkw 0x43708eea26f43f34 0xe86e11dd44de87e6 0xfff98ff83fffff1e 0xffff31ff07ffffe3

def z1147 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0x73fff0000fff6006 0x2e7ffe0001ffec00

def z1148 : W := mkw 0x035006a806d41904 0xe06a00d500da8320 0xff900ff80f9c1f06 0x9ff201ff01f383e0

def z1149 : W := mkw 0x048f7115990bc003 0x0091ee22b3217800 0x00067001c0000000 0x0000ce0038000000

def z1150 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0xfdfffffff0008319 0xffbffffffe001063

def z1151 : W := mkw 0xa0023018d80e818a 0x340046031b01d031 0x98167079f01e939b 0xf302ce0f3e03d273

def z1152 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0x77f00fb80ffc1c06 0x8efe01f701ff8380

def z1153 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0x27880f87cf831ce7 0x84f101f0f9f0639c

def z1154 : W := mkw 0x43700ee806f43f34 0xe86e01dd00de87e6 0xfff98ff80ffffffe 0xffff31ff01ffffff

def z1155 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0xfdfffffff063fce7 0xffbffffffe0c7f9c

def z1156 : W := mkw 0x05dd633593514005 0x00bbac66b26a2800 0x67fff7b9c3e16004 0x0cfffef7387c2c00

def z1157 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0xf8167c79fc1e9f9f 0xff02cf8f3f83d3f3

def z1158 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0xfff80ffe3fff9fff 0xffff01ffc7fff3ff

def z1159 : W := mkw 0x4020884220202630 0x08041108440404c6 0xf87ff8463063ffff 0xff0fff08c60c7fff

def z1160 : W := mkw 0xa0023018d80e818a 0x340046031b01d031 0xd8167479f01e8399 0xfb02ce8f3e03d073

def z1161 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0xc5fff7fff0000001 0x78bffefffe000000

def z1162 : W := mkw 0x05fdeb77b3514005 0x00bfbd6ef66a2800 0xfffffffffffd6007 0xffffffffffffac00

def z1163 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0xfbfff8060fffec66 0x7f7fff00c1fffd8c

def z1164 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0x40167479fc1e9399 0xe802ce8f3f83d273

def z1165 : W := mkw 0x45fdeb77b0002030 0x08bfbd6ef6000406 0xfdfffffff063e0ff 0xffbffffffe0c7c1f

def z1166 : W := mkw 0x800204804c821882 0xd000409009904310 0x778e0f87cf831ce7 0xaef1c1f0f9f0639c

def z1167 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0x67f00ff80ffc1f04 0x8cfe01ff01ff83e0

def z1168 : W := mkw 0x008c018501810841 0x40118030a0302108 0x278e0b87c3810c65 0x24f1c170f870218c

def z1169 : W := mkw 0x03700ee806d41904 0xe06e01dd00da8320 0x67f00fb80f9c0000 0x0cfe01f701f38000

def z1170 : W := mkw 0x03708eea26f41f04 0xe06e11dd44de83e0 0xfff98ffe3fffff07 0xffff31ffc7ffffe0

def z1171 : W := mkw 0x01700a6002700604 0x002e014c004e00c0 0xfff00ff80ffc1f06 0x9ffe01ff01ff83e0

def z1172 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0x479007f80f9c0300 0x08f200ff01f38060

def z1173 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0xfdfffffff0001303 0xffbffffffe000260

def z1174 : W := mkw 0x43708eea26f43f34 0xe86e11dd44de87e6 0xfff98ffe3ffcff1f 0xffff31ffc7ff9fe3

def z1175 : W := mkw 0x20003018900c8108 0x2400060312019021 0xd8167479f01e939b 0xfb02ce8f3e03d273

def z1176 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0x778e0f87cf810c65 0xaef1c1f0f9f0218c

def z1177 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0xd8167479fc1c8319 0xfb02ce8f3f839063

def z1178 : W := mkw 0x01dd611590000000 0x003bac22b2000000 0xf5fffffff0000001 0xfebffffffe000000

def z1179 : W := mkw 0xa1df759ddfdfd9cf 0xf43beeb3bbfbfb39 0x479677b9cf9c0000 0x08f2cef739f38000

def z1180 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0xff8e0fc7cf831fe7 0xbff1c1f8f9f063fc

def z1181 : W := mkw 0xa0023498dd8f99cb 0xf40046931bb1f339 0xda167479ff9e939b 0xfb42ce8f3ff3d273

def z1182 : W := mkw 0x01df51050b5bc007 0x003bea20a16b7800 0xffffff87cffffce7 0xfffffff0f9ffff9c

def z1183 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0xf5fffffff0010c65 0xfebffffffe00218c

def z1184 : W := mkw 0x05dde337b0000000 0x00bbbc66f6000000 0x459677bff0000001 0x08b2cef7fe000000

def z1185 : W := mkw 0x45fdeb77b0002030 0x08bfbd6ef6000406 0xf5fffffff00000f9 0xfebffffffe00001f

def z1186 : W := mkw 0x40208a6220202630 0x0804114c440404c6 0xbc698ffe3063ffff 0xf78d31ffc60c7fff

def z1187 : W := mkw 0x45fdeb77b3716635 0x08bfbd6ef66e2cc6 0xfffffffff3e3ffff 0xfffffffffe7c7fff

def z1188 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0xf5fffffff00300e1 0xfebffffffe00601c

def z1189 : W := mkw 0x80000585448018c0 0xd00000b0a8900318 0x47800f87cf801ce1 0x88f001f0f9f0039c

def z1190 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0xfbfff0403fffe007 0xff7ffe0807fffc00

def z1191 : W := mkw 0x05dd633590000000 0x00bbac66b2000000 0xf59e7ffff0000001 0xfeb3cffffe000000

def z1192 : W := mkw 0xa0002418d4041188 0xb40004831a808231 0xd8167479fc1c139b 0xfb02ce8f3f838273

def z1193 : W := mkw 0x81df51054b5bc0c7 0x103bea20a96b7818 0xffffff87cfffe0e7 0xfffffff0f9fffc1c

def z1194 : W := mkw 0x035006a806d41904 0xe06a00d500da8320 0x479007b80f9c1c06 0x08f200f701f38380

def z1195 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0xd8167479fc7ff39f 0xfb02ce8f3f8ffe73

def z1196 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0xd5967ffff0000001 0xfab2cffffe000000

def z1197 : W := mkw 0x05fdeb77b2500004 0x00bfbd6ef64a0000 0xfdfffffff07c0001 0xffbffffffe0f8000

def z1198 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0xf5fff7f9f0000000 0x7ebffeff3e000000

def z1199 : W := mkw 0xe0aeb957f92ba6fb 0x1c15d72aff2574df 0xb86ff847f063ffff 0xf70dff08fe0c7fff

def z1200 : W := mkw 0x43708eea26f43f34 0xe86e11dd44de87e6 0xfff98ffe0fff7fe7 0xbfff31ffc1ffeffc

def z1201 : W := mkw 0x44adeb77b0202630 0x0895bd6ef60404c6 0xbc6ffffff063ffff 0xf78dfffffe0c7fff

def z1202 : W := mkw 0x4571fa72b278e634 0x08ae3f4e564f1cc6 0x8871f078307ce318 0x510e3e0f060f9c63

def z1203 : W := mkw 0x05fdeb77b0200600 0x00bfbd6ef60400c0 0xf5fffffff0001f01 0xfebffffffe0003e0

def z1204 : W := mkw 0x808f55854d8bd8c3 0xd011eab0a9b17b18 0xff9fff87cf9ffce7 0xfff3fff0f9f3ff9c

def z1205 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0xf81e7c7ffc1e939b 0xff03cf8fff83d273

def z1206 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0xf78e0fc7ff831ce7 0xfef1c1f8fff0639c

def z1207 : W := mkw 0x01df51050b5bc007 0x003bea20a16b7800 0xfffffb860fffe006 0x7fffff70c1fffc00

def z1208 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0xffef8fc7ffe3ffff 0xfffdf1f8fffc7fff

def z1209 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0xfdfffffff0600007 0xffbffffffe0c0000

def z1210 : W := mkw 0x81df50004b5bc087 0x103bea00096b7810 0xfbfff001cfffe087 0x7f7ffe0039fffc10

def z1211 : W := mkw 0x03708eea26f41f04 0xe06e11dd44de83e0 0xfff98ffe0ffc1f06 0x9fff31ffc1ff83e0

def z1212 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0xebfff0000ffde004 0x5d7ffe0001ffbc00

def z1213 : W := mkw 0x035006a806f41f04 0xe06a00d500de83e0 0xfff007b80ffc1f06 0x1ffe00f701ff83e0

def z1214 : W := mkw 0x05fdeb77b0200600 0x00bfbd6ef60400c0 0xfdfffffff0631fe7 0xffbffffffe0c63fc

def z1215 : W := mkw 0x43708eea26f43f34 0xe86e11dd44de87e6 0xfff98ffe0ffffffe 0x9fff31ffc1ffffff

def z1216 : W := mkw 0x43708eea26f43f34 0xe86e11dd44de87e6 0xfff98ffe3ffd7f67 0xffff31ffc7ffafec

def z1217 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0xd877f479fc7ef39b 0xfb0efe8f3f8fde73

def z1218 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0xfff00ffe0ffc1fe7 0x9ffe01ffc1ff83fc

def z1219 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0xcbfff0000fffe000 0x797ffe0001fffc00

def z1220 : W := mkw 0x0000048804841900 0xe000009100908320 0x77900fb80f9c1c06 0x8ef201f701f38380

def z1221 : W := mkw 0x03708eea26f41f04 0xe06e11dd44de83e0 0xfff00ffe3ffc1f07 0x9ffe01ffc7ff83e0

def z1222 : W := mkw 0x0150048806d41904 0xe02a009100da8320 0xfff00ff80ffc1f06 0x9ffe01ff01ff83e0

def z1223 : W := mkw 0x40aca957b0202630 0x0815952af60404c6 0xfdfffffff063ffff 0xffbffffffe0c7fff

def z1224 : W := mkw 0x035006a806d41904 0xe06a00d500da8320 0x479007f80f9c1300 0x88f200ff01f38260

def z1225 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0xd8167479fc1f9fff 0xfb02ce8f3f83f3ff

def z1226 : W := mkw 0x0400233590000000 0x00800466b2000000 0x441677b9c0000000 0x0882cef738000000

def z1227 : W := mkw 0x43708eea26f43f34 0xe86e11dd44de87e6 0xfff98ffe3ffdff7e 0xdfff31ffc7ffbfef

def z1228 : W := mkw 0x808f55854d8bd8c3 0xd011eab0a9b17b18 0x778e7f87cf831ce7 0xaef1cff0f9f0639c

def z1229 : W := mkw 0x808c0585458118c1 0xd01180b0a8b02318 0x778e0f87c3811ce5 0xaef1c1f0f870239c

def z1230 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0xf5fffffff0030007 0xfebffffffe006000

def z1231 : W := mkw 0xa20214884fff9fcf 0xf440429109fff3f9 0x0a0000000fff9ffe 0x0140000001fff3ff

def z1232 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0xf7f00ff80f9c1f00 0x9efe01ff01f383e0

def z1233 : W := mkw 0x01700ee804841900 0xe02e01dd00908320 0xfff00ff80f9c1f06 0x9ffe01ff01f383e0

def z1234 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0xfff60ff9cffc1f07 0xbffec1ff39ff83e0

def z1235 : W := mkw 0x008c211590000000 0x00118422b2000000 0xd59677f9f0000001 0xfab2ceff3e000000

def z1236 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0x278e0f87c3831ce5 0xa4f1c1f0f870639c

def z1237 : W := mkw 0x4020884220202630 0x08041108440404c6 0x286988463063ffff 0x850d3108c60c7fff

def z1238 : W := mkw 0x01700a6002500004 0x002e014c004a0000 0xf7f00ff80f9c0000 0x9efe01ff01f38000

def z1239 : W := mkw 0x03700ee806d41904 0xe06e01dd00da8320 0xc7f007f80f9c0000 0x18fe00ff01f38000

def z1240 : W := mkw 0x03708eea26d41904 0xe06e11dd44da8320 0xf7f98ffe3f9c0001 0xfeff31ffc7f38000

def z1241 : W := mkw 0x6370ba7ab27ca73c 0x2c6e174f564f94e7 0x8871f078307ce318 0x510e3e0f060f9c63

def z1242 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0xfb967479ff9e939f 0xff72ce8f3ff3d273

def z1243 : W := mkw 0x0571eb77b0000000 0x00ae3d6ef6000000 0xd477fffff0000001 0xfa8efffffe000000

def z1244 : W := mkw 0x03708eea26f41f04 0xe06e11dd44de83e0 0xfff98ffe3fff1fe7 0xffff31ffc7ffe3fc

def z1245 : W := mkw 0x01702a7090000000 0x002e054e12000000 0xf5f67ff9c0000000 0x9ebecfff38000000

def z1246 : W := mkw 0x43708eea26f43f34 0xe86e11dd44de87e6 0xfff00ff83ffc1f1e 0x9ffe01ff07ff83e3

def z1247 : W := mkw 0x05fdeb77b2500004 0x00bfbd6ef64a0000 0xf7fffffff3e00005 0xfefffffffe7c0000

def z1248 : W := mkw 0x008c018501810841 0x40118030a0302108 0x27880f87c3810c65 0x84f101f0f870218c

def z1249 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0xf87ffc7ffc7fffff 0xff0fff8fff8fffff

def z1250 : W := mkw 0x01df50000b5bc007 0x003bea00016b7800 0xfbfff0000ffffce6 0x7f7ffe0001ffff9c

def z1251 : W := mkw 0x015350000b5bc007 0x002a6a00016b7800 0xda77f0000fffe006 0x7b4efe0001fffc00

def z1252 : W := mkw 0x808e05854d8318c3 0xd011c0b0a9b06318 0xff9e0f87cf9f1ce7 0xbff3c1f0f9f3e39c

def z1253 : W := mkw 0x43700ee806f43f34 0xe86e01dd00de87e6 0xfff00ff80ffc1ffe 0x9ffe01ff01ff83ff

def z1254 : W := mkw 0x05fdeb77b2504004 0x00bfbd6ef64a0800 0xf5fffffff0606001 0xfebffffffe0c0c00

def z1255 : W := mkw 0xa00214884c8e99ca 0xf40042910991d339 0x080000000c1e9ffa 0x010000000183d3ff

def z1256 : W := mkw 0x05dd633590000000 0x00bbac66b2000000 0x65fff7b9c0000000 0x0cbffef738000000

def z1257 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0xfdfffffffc1c0003 0xffbfffffff838000

def z1258 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0xfff00ff80ffe9f06 0xfffe01ff01ffd3e0

def z1259 : W := mkw 0x03700ee806f41f04 0xe06e01dd00de83e0 0xfff00ff83ffc1f07 0xfffe01ff07ff83e0

def z1260 : W := mkw 0xa08f7115d90bc0cb 0x1411ee22bb217819 0x000ff007f003e0f9 0x6001fe00fe007c1f

def z1261 : W := mkw 0xa08e3115d90b80cb 0x1411c622bb217019 0x000e7007c00300e1 0x2001ce00f800601c

def z1262 : W := mkw 0x4020884220202630 0x08041108440404c6 0xfbe988463fe3ffff 0xff7d3108c7fc7fff

def z1263 : W := mkw 0x05fdeb77b0000000 0x00bfbd6ef6000000 0xf5fffffff0001ce1 0xfebffffffe00039c

def z1264 : W := mkw 0x808e15854d8b98c3 0xd011c2b0a9b17318 0xff9e7fc7ff9f9fff 0xfff3cff8fff3f3ff

def z1265 : W := mkw 0x05fdeb77b3514005 0x00bfbd6ef66a2800 0xfffffffff3e3e007 0xfffffffffe7c7c00

def z1266 : W := mkw 0x008c058505811841 0xc01180b0a0b02308 0x778e0f87cf811c67 0xaef1c1f0f9f0238c

def z1267 : W := mkw 0xa0023418dc0e918a 0xb40046831b81d231 0xd81e747ffc1f93fb 0xfb03ce8fff83f27f

def z1268 : W := mkw 0xa08e058d4d8719cb 0xf411c0b1a9b0e339 0x778e0f87cf831fff 0xaef1c1f0f9f063ff

def z1269 : W := mkw 0x820214884fffdfc7 0xf040429109fffbf8 0x0a0000000fffffe6 0x0140000001fffffc

def z1270 : W := mkw 0x45fdeb77b0002030 0x08bfbd6ef6000406 0xf5fffffff000e019 0xfebffffffe001c03

def z1271 : W := mkw 0x05dde337b0000000 0x00bbbc66f6000000 0x4597f7b9f0000000 0x48b2fef73e000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z0,z1,z3,z4,z5,z6]),(1,[z8,z9,z3,z10,z5,z6]),(0,[z11,z0,z9,z3,z4,z5,z6]),(1,[z12,z0,z9,z3,z5,z13])],[(1,[z0,z9,z14,z4,z5,z6]),(0,[z0,z9,z4,z15,z5,z16,z6]),(0,[z0,z9,z17,z4,z5,z18,z6])],[(0,[z19,z0,z9,z3,z4,z5,z6]),(0,[z20,z0,z9,z21,z4,z5,z6]),(0,[z0,z3,z4,z22,z23,z5,z6]),(0,[z0,z9,z24,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z25,z6])],[(0,[z0,z9,z26,z3,z4,z5,z6]),(0,[z27,z0,z9,z3,z4,z5,z6]),(0,[z0,z28,z9,z3,z4,z5,z6])],[(0,[z7,z0,z9,z21,z4,z5,z6]),(0,[z29,z0,z9,z3,z22,z5,z6]),(0,[z30,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z31])],[(0,[z0,z9,z3,z32,z4,z5,z6]),(0,[z0,z1,z3,z4,z33,z5,z6]),(0,[z27,z0,z9,z3,z4,z5,z34])],[(0,[z0,z1,z3,z4,z5,z35,z6]),(1,[z0,z9,z36,z4,z5,z6]),(0,[z37,z0,z1,z3,z4,z5,z6]),(1,[z38,z0,z3,z4,z5,z39]),(0,[z40,z0,z9,z4,z15,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z41])],[(1,[z0,z9,z3,z4,z5,z42]),(0,[z43,z9,z3,z44,z4,z5,z6]),(0,[z0,z9,z3,z4,z45,z5,z6]),(0,[z46,z0,z9,z3,z4,z5,z6]),(0,[z37,z47,z9,z3,z4,z5,z6])]],
   [[(0,[z48,z0,z9,z3,z4,z5,z6]),(0,[z12,z0,z3,z4,z22,z5,z6]),(0,[z37,z0,z9,z3,z4,z49,z6]),(0,[z20,z0,z9,z3,z4,z5,z50])],[(0,[z51,z52,z9,z3,z4,z5,z6]),(0,[z20,z0,z9,z53,z4,z5,z6]),(0,[z0,z9,z3,z4,z54,z5,z6]),(0,[z55,z0,z9,z3,z4,z35,z6]),(0,[z9,z3,z4,z5,z16,z6,z56]),(0,[z0,z57,z9,z3,z4,z5,z6]),(0,[z0,z3,z4,z22,z5,z6,z58]),(0,[z0,z1,z3,z4,z5,z59,z6]),(0,[z0,z9,z17,z4,z15,z5,z6]),(0,[z0,z9,z17,z60,z4,z5,z6])],[(0,[z0,z9,z3,z61,z4,z5,z6]),(0,[z0,z62,z9,z3,z4,z5,z6]),(0,[z0,z3,z4,z22,z5,z63,z6]),(0,[z64,z0,z9,z65,z3,z4,z6]),(0,[z0,z9,z3,z4,z66,z5,z6])],[(0,[z7,z0,z9,z53,z4,z5,z6]),(0,[z0,z9,z3,z67,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z68]),(0,[z0,z1,z65,z3,z4,z5,z6]),(0,[z69,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z70,z6])],[(0,[z0,z71,z9,z3,z4,z5,z6]),(0,[z0,z9,z72,z3,z4,z5,z6]),(0,[z73,z0,z9,z3,z5,z6,z74])],[(0,[z52,z9,z3,z4,z75,z5,z6]),(0,[z76,z0,z9,z3,z4,z77,z6]),(0,[z0,z1,z3,z4,z4,z5,z6]),(0,[z78,z0,z9,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z23,z5,z6]),(0,[z0,z79,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z80,z6]),(0,[z0,z9,z17,z4,z5,z25,z6]),(0,[z0,z81,z9,z3,z4,z5,z6])],[(0,[z82,z0,z9,z3,z4,z5,z6]),(0,[z9,z3,z53,z4,z5,z35,z6]),(0,[z83,z0,z9,z3,z4,z5,z6]),(0,[z20,z0,z9,z4,z5,z6,z50]),(1,[z0,z84,z3,z4,z5,z6])]],
   [[(0,[z76,z85,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z86]),(0,[z0,z3,z4,z22,z5,z6,z13]),(0,[z87,z0,z9,z17,z4,z5,z6]),(0,[z0,z9,z3,z4,z88,z5,z6])],[(0,[z0,z89,z9,z3,z4,z5,z6]),(0,[z0,z9,z17,z32,z4,z5,z6]),(0,[z0,z3,z4,z22,z5,z25,z6])],[(0,[z27,z0,z9,z4,z15,z5,z6]),(0,[z0,z9,z4,z15,z90,z5,z6]),(0,[z0,z9,z3,z91,z4,z5,z13])],[(0,[z51,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z92,z5,z6]),(0,[z0,z62,z9,z4,z5,z93,z6]),(1,[z0,z1,z3,z4,z5,z6]),(0,[z94,z0,z9,z3,z4,z5,z6]),(0,[z95,z0,z9,z3,z4,z5,z6])],[(0,[z51,z96,z0,z3,z4,z5,z6]),(0,[z0,z9,z97,z3,z4,z5,z6]),(0,[z0,z9,z3,z98,z4,z5,z6]),(1,[z47,z9,z3,z4,z5,z6]),(0,[z0,z9,z99,z3,z4,z5,z6]),(0,[z12,z0,z9,z100,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z58]),(0,[z38,z0,z9,z17,z4,z5,z6]),(0,[z0,z9,z3,z4,z101,z5,z6])],[(0,[z102,z0,z9,z3,z4,z5,z6]),(0,[z103,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z104,z6]),(0,[z0,z1,z3,z105,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z106,z58]),(0,[z0,z9,z3,z4,z5,z6,z107])],[(0,[z0,z9,z3,z4,z5,z108,z6]),(0,[z0,z109,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z110]),(0,[z0,z9,z3,z4,z111,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z112]),(0,[z113,z0,z9,z3,z4,z5,z6]),(0,[z114,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z115,z5,z6])]],
   [[(0,[z116,z0,z9,z3,z4,z5,z6]),(0,[z0,z3,z44,z4,z22,z5,z6]),(0,[z85,z0,z9,z3,z4,z5,z6]),(0,[z117,z0,z9,z3,z4,z5,z6]),(0,[z118,z0,z9,z3,z4,z5,z6]),(0,[z119,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z93,z6,z120]),(0,[z0,z9,z3,z121,z4,z122,z6])],[(0,[z0,z9,z3,z4,z123,z5,z6]),(0,[z64,z0,z9,z3,z4,z124,z6]),(0,[z0,z9,z3,z4,z5,z6,z125]),(0,[z0,z9,z3,z122,z5,z6,z74])],[(0,[z0,z126,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z127,z6]),(0,[z0,z9,z3,z128,z4,z5,z6]),(0,[z8,z0,z9,z3,z4,z129,z6]),(1,[z130,z9,z3,z4,z5,z6])],[(0,[z0,z9,z3,z4,z5,z6,z56]),(0,[z29,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z4,z15,z5,z6,z39]),(1,[z0,z9,z131,z4,z5,z6]),(1,[z0,z9,z3,z4,z23,z58])],[(0,[z0,z9,z3,z132,z4,z5,z6]),(1,[z0,z9,z3,z4,z133,z6]),(0,[z43,z0,z3,z4,z22,z5,z6]),(0,[z0,z62,z3,z4,z22,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z13]),(0,[z0,z9,z134,z3,z4,z5,z6])],[(1,[z0,z9,z135,z4,z5,z6]),(0,[z0,z9,z3,z4,z136,z5,z6]),(0,[z0,z1,z3,z4,z5,z25,z6]),(0,[z0,z9,z3,z4,z137,z5,z6]),(0,[z0,z9,z3,z4,z138,z5,z6]),(0,[z20,z0,z9,z3,z4,z5,z6])],[(0,[z139,z0,z9,z3,z4,z5,z6]),(0,[z52,z0,z3,z4,z22,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z140]),(0,[z0,z9,z141,z3,z4,z5,z50]),(0,[z142,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z143])],[(0,[z51,z0,z144,z3,z4,z5,z6]),(0,[z7,z0,z9,z3,z4,z5,z6]),(0,[z43,z0,z9,z3,z44,z5,z6]),(0,[z145,z0,z9,z3,z4,z5,z6])]],
   [[(1,[z146,z144,z3,z4,z5,z6]),(0,[z0,z9,z147,z3,z4,z5,z6]),(0,[z0,z9,z4,z15,z75,z5,z6]),(0,[z0,z9,z3,z4,z148,z5,z6]),(0,[z20,z0,z9,z3,z4,z5,z93]),(0,[z0,z9,z3,z4,z5,z149,z6])],[(1,[z0,z9,z3,z4,z5,z150]),(0,[z73,z0,z151,z3,z4,z5,z6]),(1,[z0,z3,z4,z5,z6,z152])],[(0,[z51,z0,z9,z4,z15,z5,z6]),(0,[z153,z0,z9,z3,z4,z5,z6]),(1,[z0,z1,z4,z15,z5,z6]),(0,[z20,z0,z9,z141,z4,z5,z6]),(0,[z154,z0,z9,z3,z4,z5,z6])],[(0,[z144,z9,z2,z3,z4,z5,z6]),(0,[z0,z9,z3,z155,z4,z5,z6]),(0,[z0,z9,z3,z156,z4,z5,z6])],[(0,[z0,z9,z3,z4,z5,z157,z6]),(0,[z0,z3,z32,z4,z22,z5,z6]),(0,[z0,z3,z4,z158,z22,z5,z6]),(0,[z0,z9,z3,z4,z33,z6,z58]),(0,[z0,z159,z9,z3,z4,z5,z39]),(0,[z160,z0,z9,z3,z4,z5,z6]),(1,[z0,z9,z4,z161,z5,z6]),(1,[z0,z9,z162,z4,z5,z6])],[(0,[z51,z0,z3,z4,z22,z5,z6]),(0,[z8,z9,z3,z4,z10,z5,z6]),(0,[z163,z0,z9,z3,z4,z5,z6]),(0,[z29,z0,z9,z164,z4,z5,z6]),(0,[z165,z0,z9,z17,z4,z5,z6]),(0,[z37,z0,z9,z3,z4,z5,z6]),(0,[z166,z0,z9,z3,z4,z5,z6])],[(0,[z167,z0,z1,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z168]),(0,[z169,z0,z9,z3,z4,z5,z6])],[(0,[z170,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z17,z4,z5,z6,z56]),(0,[z0,z171,z9,z3,z4,z5,z6]),(0,[z0,z172,z9,z17,z4,z5,z6]),(0,[z0,z9,z4,z5,z93,z6,z50]),(0,[z173,z0,z9,z3,z4,z5,z6]),(0,[z12,z0,z9,z3,z4,z174,z6])]],
   [[(0,[z0,z9,z3,z175,z4,z5,z6]),(0,[z0,z9,z3,z4,z176,z5,z6]),(0,[z96,z0,z9,z4,z5,z93,z6]),(0,[z0,z9,z4,z5,z6,z177,z39]),(0,[z0,z9,z3,z4,z5,z6,z178])],[(0,[z144,z9,z3,z4,z5,z35,z6]),(0,[z0,z9,z3,z4,z179,z5,z6])],[(0,[z167,z0,z9,z21,z4,z5,z6]),(0,[z0,z180,z9,z3,z4,z5,z6]),(0,[z0,z3,z4,z22,z5,z6,z56]),(0,[z0,z9,z3,z4,z5,z181,z6]),(0,[z85,z0,z3,z4,z22,z5,z6]),(0,[z182,z0,z9,z3,z4,z5,z6]),(0,[z29,z0,z9,z4,z15,z5,z6]),(1,[z0,z9,z183,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z184]),(0,[z0,z9,z65,z3,z4,z6,z58])],[(0,[z0,z9,z185,z3,z4,z5,z6]),(0,[z73,z0,z9,z3,z4,z5,z186]),(0,[z64,z0,z9,z3,z4,z5,z58])],[(0,[z0,z9,z3,z4,z5,z6,z187]),(0,[z0,z9,z3,z4,z5,z188,z6]),(0,[z20,z0,z9,z4,z15,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z189])],[(0,[z0,z9,z3,z4,z190,z5,z6]),(0,[z76,z0,z1,z3,z4,z5,z6]),(0,[z139,z0,z9,z4,z15,z5,z6]),(1,[z37,z0,z9,z4,z49,z6]),(0,[z0,z9,z3,z4,z23,z6,z58])],[(0,[z7,z0,z9,z4,z15,z5,z6]),(0,[z0,z9,z3,z191,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z192,z6]),(1,[z0,z3,z4,z193,z5,z6])],[(0,[z51,z0,z2,z3,z4,z5,z6]),(0,[z0,z194,z3,z53,z4,z5,z6]),(0,[z8,z0,z9,z3,z4,z5,z42]),(0,[z0,z3,z4,z22,z148,z5,z6]),(0,[z20,z0,z3,z4,z22,z5,z6]),(0,[z195,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z196,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z197]),(0,[z0,z9,z4,z5,z198,z6,z58])]],
   [[(0,[z146,z51,z9,z3,z4,z5,z6]),(0,[z199,z0,z9,z3,z4,z5,z6]),(0,[z200,z0,z9,z3,z4,z5,z6]),(0,[z0,z47,z9,z3,z4,z5,z6])],[(0,[z167,z0,z9,z53,z4,z5,z6]),(0,[z201,z0,z9,z3,z4,z5,z6]),(0,[z8,z43,z9,z3,z4,z5,z6]),(0,[z96,z0,z3,z4,z22,z5,z6]),(0,[z202,z0,z9,z3,z4,z5,z6]),(0,[z203,z0,z9,z3,z4,z5,z6])],[(1,[z0,z9,z3,z4,z5,z6]),(0,[z146,z0,z1,z3,z4,z5,z6]),(0,[z0,z204,z9,z3,z4,z5,z6]),(0,[z0,z3,z4,z22,z5,z6,z50]),(0,[z0,z9,z121,z4,z15,z5,z6])],[(0,[z205,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z206,z53,z4,z5,z6]),(0,[z207,z0,z9,z3,z4,z5,z6]),(0,[z9,z3,z4,z10,z5,z35,z6]),(0,[z9,z3,z4,z75,z5,z35,z6]),(0,[z0,z9,z141,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z186,z6])],[(0,[z0,z208,z9,z3,z4,z5,z6]),(0,[z0,z9,z21,z206,z4,z5,z6]),(1,[z0,z9,z3,z4,z5,z34]),(0,[z37,z0,z9,z4,z15,z5,z6]),(0,[z12,z0,z9,z3,z4,z115,z6]),(0,[z209,z0,z9,z3,z4,z5,z6])],[(0,[z210,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z211,z6]),(0,[z0,z212,z9,z3,z4,z5,z6]),(0,[z96,z0,z62,z3,z4,z5,z6]),(0,[z0,z3,z4,z22,z5,z6,z168]),(0,[z0,z9,z3,z4,z5,z213,z6]),(0,[z20,z37,z0,z9,z4,z5,z6])],[(0,[z214,z0,z9,z3,z4,z5,z6]),(0,[z27,z0,z9,z3,z4,z75,z6]),(0,[z0,z1,z3,z4,z5,z6,z56]),(0,[z215,z0,z1,z3,z4,z5,z6]),(0,[z0,z216,z9,z3,z4,z124,z6]),(0,[z0,z9,z217,z17,z4,z5,z6]),(0,[z0,z9,z4,z218,z5,z93,z6])],[(0,[z219,z0,z9,z3,z4,z5,z6]),(0,[z0,z220,z9,z3,z4,z5,z6]),(0,[z52,z0,z9,z3,z4,z35,z6]),(0,[z0,z9,z3,z4,z221,z5,z6]),(0,[z0,z9,z3,z222,z4,z5,z6]),(0,[z223,z0,z9,z4,z5,z6,z58]),(0,[z0,z9,z224,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z53,z4,z5,z6]),(0,[z0,z225,z9,z3,z4,z5,z6]),(0,[z55,z9,z3,z4,z5,z35,z6]),(0,[z0,z9,z3,z4,z226,z5,z6]),(0,[z0,z9,z3,z4,z5,z227,z6]),(0,[z73,z0,z84,z3,z4,z5,z6])],[(0,[z0,z9,z228,z3,z4,z5,z6]),(0,[z229,z0,z9,z3,z4,z5,z6])],[(0,[z0,z9,z21,z32,z4,z5,z6]),(1,[z0,z9,z3,z4,z5,z157]),(0,[z0,z9,z3,z4,z5,z230,z6]),(0,[z231,z0,z9,z3,z4,z5,z6]),(0,[z37,z0,z9,z3,z4,z218,z6]),(0,[z0,z9,z3,z4,z5,z93,z6]),(1,[z0,z9,z141,z4,z5,z93])],[(0,[z167,z52,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z232]),(0,[z0,z9,z233,z3,z4,z5,z6]),(0,[z0,z9,z3,z164,z4,z5,z6])],[(0,[z0,z9,z3,z4,z5,z6,z234]),(0,[z55,z0,z9,z17,z4,z5,z6]),(1,[z0,z9,z164,z4,z5,z6]),(0,[z0,z3,z4,z22,z5,z124,z6]),(0,[z73,z0,z1,z3,z4,z5,z6]),(0,[z27,z0,z9,z3,z4,z33,z6]),(0,[z38,z27,z0,z3,z4,z5,z6]),(0,[z0,z9,z3,z235,z4,z5,z6]),(0,[z0,z9,z141,z4,z5,z93,z6])],[(0,[z85,z9,z3,z4,z5,z16,z6]),(0,[z236,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z237]),(0,[z0,z9,z3,z4,z238,z5,z6])],[(0,[z239,z0,z9,z3,z4,z5,z6]),(0,[z8,z0,z9,z3,z10,z5,z6]),(0,[z8,z0,z9,z17,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z50]),(0,[z0,z9,z4,z15,z23,z5,z6])],[(0,[z0,z9,z240,z3,z4,z5,z6]),(0,[z0,z9,z241,z17,z4,z5,z6]),(0,[z0,z9,z242,z3,z4,z5,z6])]],
   [[(0,[z243,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z244,z3,z4,z5,z6]),(0,[z0,z9,z245,z3,z4,z5,z6]),(0,[z246,z0,z9,z3,z4,z5,z6]),(0,[z20,z96,z0,z9,z4,z5,z6]),(0,[z247,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z248,z5,z6]),(0,[z0,z9,z91,z4,z15,z5,z6]),(0,[z0,z9,z3,z4,z5,z249,z6]),(1,[z250,z0,z3,z4,z5,z6])],[(0,[z0,z9,z3,z4,z251,z5,z6]),(0,[z252,z0,z9,z3,z4,z5,z6]),(0,[z0,z253,z9,z3,z4,z5,z6]),(0,[z38,z0,z9,z3,z4,z254,z6]),(1,[z0,z9,z4,z15,z5,z6]),(1,[z0,z9,z3,z4,z5,z31])],[(0,[z0,z9,z3,z4,z5,z255,z6]),(0,[z256,z0,z9,z3,z4,z5,z6]),(1,[z29,z0,z3,z22,z5,z6]),(0,[z0,z1,z9,z17,z4,z5,z6]),(0,[z257,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z4,z15,z258,z5,z6]),(0,[z0,z9,z141,z4,z15,z5,z6]),(0,[z0,z9,z17,z141,z4,z5,z6])],[(0,[z0,z9,z2,z17,z4,z5,z6]),(0,[z8,z0,z9,z3,z4,z259,z6]),(0,[z0,z9,z3,z4,z5,z260,z6]),(0,[z73,z130,z9,z3,z4,z5,z6]),(0,[z0,z9,z162,z3,z4,z5,z6])],[(0,[z0,z9,z3,z4,z261,z5,z6]),(0,[z0,z9,z3,z4,z5,z262,z6]),(0,[z0,z3,z44,z4,z45,z5,z6]),(0,[z263,z0,z9,z3,z4,z5,z6]),(0,[z0,z3,z4,z33,z5,z124,z6])],[(0,[z167,z0,z9,z3,z4,z5,z6]),(0,[z264,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z129,z5,z6]),(0,[z0,z9,z3,z4,z5,z265,z6]),(0,[z0,z9,z4,z15,z5,z6,z58])],[(0,[z0,z9,z3,z4,z5,z6,z266]),(0,[z0,z9,z3,z267,z4,z5,z6]),(0,[z0,z9,z17,z4,z5,z93,z6])],[(0,[z0,z9,z206,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z268,z5,z6])]],
   [[(0,[z0,z9,z269,z44,z4,z5,z6]),(0,[z0,z1,z3,z270,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z124,z6]),(0,[z0,z9,z17,z3,z15,z5,z6])],[(0,[z0,z144,z1,z3,z4,z5,z6]),(0,[z271,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z272,z4,z5,z6]),(1,[z273,z0,z9,z4,z5,z6]),(0,[z0,z9,z4,z4,z15,z5,z6]),(0,[z0,z9,z3,z91,z4,z5,z6])],[(0,[z0,z9,z3,z4,z274,z5,z6]),(0,[z0,z9,z53,z32,z4,z5,z6]),(1,[z96,z0,z32,z4,z5,z6]),(0,[z64,z0,z1,z3,z4,z5,z6]),(0,[z0,z275,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z276,z5,z6])],[(0,[z0,z9,z3,z4,z5,z6,z277]),(0,[z0,z9,z3,z44,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z278,z6]),(1,[z0,z279,z3,z4,z5,z6])],[(0,[z280,z0,z9,z3,z4,z5,z6]),(0,[z0,z159,z9,z3,z4,z5,z106]),(0,[z0,z9,z4,z15,z5,z6,z13]),(0,[z0,z9,z3,z4,z281,z5,z6]),(1,[z0,z9,z3,z4,z6,z120]),(0,[z64,z0,z9,z3,z4,z6,z74])],[(0,[z282,z0,z9,z3,z4,z5,z6]),(1,[z0,z9,z4,z54,z5,z6]),(0,[z0,z9,z3,z283,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z284]),(0,[z0,z9,z4,z15,z5,z285,z6]),(0,[z73,z0,z9,z286,z4,z5,z6]),(1,[z0,z81,z3,z4,z5,z6])],[(0,[z0,z0,z9,z3,z4,z5,z6]),(0,[z287,z0,z3,z53,z4,z5,z6]),(0,[z9,z3,z44,z4,z10,z5,z6]),(0,[z0,z9,z3,z288,z4,z5,z6]),(0,[z0,z1,z141,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z289]),(0,[z0,z9,z65,z17,z4,z5,z6]),(0,[z290,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z291])],[(0,[z0,z3,z4,z22,z15,z5,z6]),(0,[z0,z141,z3,z4,z22,z5,z6]),(0,[z38,z0,z9,z3,z4,z5,z39]),(0,[z0,z9,z4,z292,z15,z5,z6]),(0,[z0,z9,z3,z4,z5,z293,z6]),(0,[z0,z9,z3,z100,z4,z5,z6])]],
   [[(0,[z0,z9,z3,z294,z4,z5,z6]),(0,[z64,z0,z9,z3,z4,z122,z6]),(0,[z250,z0,z9,z3,z4,z5,z6])],[(0,[z295,z0,z9,z3,z4,z5,z6]),(0,[z52,z9,z3,z4,z10,z5,z6]),(0,[z0,z9,z3,z4,z5,z296,z6]),(0,[z0,z9,z3,z297,z4,z5,z6])],[(0,[z146,z96,z0,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z298]),(0,[z299,z0,z9,z3,z4,z5,z6]),(0,[z247,z0,z3,z4,z22,z5,z6])],[(0,[z0,z9,z3,z4,z300,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z301]),(0,[z302,z0,z9,z3,z4,z5,z6]),(0,[z37,z113,z9,z3,z4,z5,z6])],[(0,[z167,z0,z9,z4,z15,z5,z6]),(0,[z0,z9,z3,z4,z5,z106,z6]),(0,[z12,z0,z9,z17,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z120])],[(0,[z146,z0,z206,z3,z4,z5,z6]),(1,[z0,z194,z3,z4,z5,z6]),(1,[z76,z9,z3,z4,z5,z56]),(0,[z0,z1,z3,z4,z5,z93,z6]),(0,[z0,z9,z294,z4,z15,z5,z6]),(0,[z0,z9,z17,z91,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z303,z6])],[(0,[z0,z9,z304,z3,z4,z5,z6]),(1,[z0,z225,z3,z4,z5,z6]),(0,[z0,z9,z206,z4,z15,z5,z6]),(0,[z0,z9,z305,z3,z4,z5,z6])],[(0,[z0,z9,z3,z4,z5,z6,z306]),(1,[z167,z9,z21,z4,z5,z6]),(0,[z0,z9,z17,z44,z4,z5,z6]),(1,[z0,z4,z22,z15,z5,z6]),(0,[z0,z9,z3,z121,z4,z6,z74]),(0,[z0,z9,z3,z307,z4,z5,z6])]],
   [[(0,[z0,z9,z308,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z309,z6]),(0,[z0,z9,z3,z4,z35,z6,z58]),(0,[z0,z9,z3,z4,z310,z5,z6]),(0,[z0,z9,z3,z311,z4,z5,z6]),(0,[z27,z0,z3,z4,z22,z5,z6]),(0,[z0,z1,z17,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z312,z5,z6]),(0,[z0,z313,z9,z3,z4,z5,z6])],[(0,[z314,z0,z9,z3,z4,z5,z6]),(0,[z315,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z316,z4,z5,z6]),(0,[z0,z9,z3,z317,z4,z5,z6]),(1,[z318,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z319]),(0,[z0,z9,z3,z91,z5,z25,z6]),(0,[z0,z9,z3,z4,z5,z6,z320])],[(0,[z0,z9,z321,z3,z4,z5,z6]),(0,[z8,z0,z204,z3,z4,z5,z6]),(1,[z0,z9,z245,z4,z5,z6]),(0,[z322,z0,z9,z3,z4,z5,z6]),(0,[z323,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z17,z288,z4,z5,z6]),(0,[z0,z9,z3,z324,z4,z5,z6]),(0,[z0,z159,z3,z4,z5,z106,z6]),(0,[z0,z9,z17,z4,z5,z6,z289])],[(0,[z96,z0,z3,z32,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z325,z6]),(0,[z0,z1,z3,z4,z5,z326,z6]),(0,[z0,z1,z3,z4,z15,z5,z6]),(0,[z0,z3,z4,z5,z106,z6,z39]),(0,[z0,z327,z9,z3,z4,z5,z6])],[(1,[z7,z9,z53,z4,z5,z6]),(0,[z0,z9,z328,z3,z4,z5,z6]),(0,[z76,z9,z3,z4,z5,z6,z56]),(0,[z0,z9,z329,z3,z4,z5,z6]),(1,[z9,z3,z4,z5,z213,z6]),(0,[z0,z9,z17,z294,z4,z5,z6]),(0,[z0,z9,z4,z218,z5,z49,z6]),(0,[z0,z151,z9,z3,z4,z5,z6]),(0,[z0,z279,z3,z91,z4,z5,z6])],[(0,[z146,z0,z144,z3,z4,z5,z6]),(0,[z167,z9,z21,z3,z4,z5,z6]),(0,[z85,z9,z3,z4,z10,z5,z6]),(0,[z52,z43,z9,z3,z4,z5,z6]),(0,[z330,z0,z9,z3,z4,z5,z6]),(1,[z0,z9,z3,z4,z331,z6]),(0,[z0,z9,z270,z4,z15,z5,z6]),(1,[z332,z9,z3,z4,z5,z6])],[(0,[z0,z9,z288,z4,z333,z5,z6]),(0,[z302,z0,z9,z3,z15,z5,z6]),(1,[z0,z334,z3,z4,z5,z6]),(0,[z0,z9,z3,z335,z4,z5,z6]),(0,[z0,z9,z3,z4,z122,z5,z6])],[(1,[z0,z336,z3,z4,z5,z6]),(0,[z0,z9,z17,z337,z4,z5,z6]),(0,[z338,z0,z9,z3,z4,z5,z6]),(1,[z0,z9,z335,z4,z5,z6])]],
   [[(0,[z339,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z17,z4,z5,z106,z6]),(1,[z113,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z49,z6]),(0,[z0,z9,z65,z4,z218,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z74])],[(0,[z340,z0,z9,z3,z4,z5,z6])],[(0,[z302,z0,z9,z4,z15,z5,z6]),(0,[z341,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z342,z6])],[(0,[z0,z9,z3,z343,z4,z5,z6]),(0,[z9,z3,z4,z10,z5,z6,z56]),(0,[z0,z1,z3,z32,z4,z5,z6]),(0,[z344,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z84,z3,z4,z5,z6]),(0,[z0,z9,z3,z345,z4,z5,z6])],[(0,[z346,z0,z9,z3,z4,z5,z6]),(0,[z43,z9,z3,z4,z5,z35,z6]),(0,[z0,z1,z3,z91,z4,z5,z6]),(1,[z302,z0,z9,z15,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z347])],[(0,[z0,z9,z3,z348,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z349]),(0,[z302,z0,z3,z4,z22,z5,z6]),(0,[z165,z0,z1,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z331,z6])],[(0,[z0,z9,z3,z4,z5,z350,z6]),(0,[z0,z9,z21,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z58,z39]),(0,[z0,z9,z3,z4,z351,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z352]),(1,[z353,z9,z3,z4,z5,z6])],[(0,[z51,z9,z2,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z133,z6]),(0,[z0,z9,z3,z4,z5,z16,z25]),(1,[z27,z0,z3,z4,z124,z6]),(0,[z27,z0,z3,z4,z5,z124,z6]),(0,[z354,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z355,z4,z5,z6]),(0,[z0,z9,z3,z270,z4,z6,z58])]],
   [[(0,[z0,z144,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z356,z5,z6]),(0,[z43,z0,z9,z17,z4,z5,z6]),(0,[z0,z9,z3,z4,z357,z5,z6]),(0,[z0,z62,z9,z17,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z358]),(0,[z314,z0,z9,z4,z15,z5,z6])],[(0,[z85,z43,z9,z3,z4,z5,z6]),(0,[z76,z0,z9,z3,z4,z5,z16]),(0,[z0,z3,z288,z4,z22,z5,z6]),(0,[z0,z1,z3,z288,z4,z5,z6]),(0,[z359,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z360,z5,z6]),(0,[z0,z3,z91,z4,z193,z5,z6]),(0,[z64,z0,z9,z3,z4,z5,z6])],[(0,[z0,z9,z361,z3,z4,z5,z6]),(0,[z52,z0,z9,z17,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z362,z6]),(0,[z363,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z17,z4,z122,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z364])],[(1,[z55,z9,z3,z4,z35,z6]),(0,[z314,z0,z3,z4,z22,z5,z6]),(0,[z0,z3,z4,z22,z123,z5,z6]),(0,[z0,z3,z4,z33,z5,z106,z6]),(0,[z365,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z366,z5,z6]),(0,[z12,z0,z9,z367,z4,z5,z6]),(0,[z0,z9,z3,z5,z25,z6,z13]),(1,[z64,z0,z9,z3,z270,z4])],[(0,[z8,z0,z9,z14,z4,z5,z6]),(0,[z0,z9,z17,z4,z5,z6,z74]),(0,[z0,z9,z17,z4,z5,z49,z6])],[(0,[z0,z9,z3,z4,z5,z6,z368]),(0,[z0,z9,z3,z369,z4,z5,z6]),(0,[z0,z3,z4,z22,z122,z5,z6]),(0,[z0,z334,z3,z294,z4,z5,z6]),(0,[z370,z0,z9,z3,z4,z5,z6])],[(0,[z0,z9,z3,z4,z5,z371,z6]),(0,[z0,z9,z372,z3,z4,z5,z6]),(0,[z373,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z4,z15,z5,z6,z50]),(0,[z223,z0,z9,z3,z4,z5,z6])],[(0,[z0,z9,z21,z4,z5,z93,z6]),(0,[z0,z3,z4,z374,z22,z5,z6]),(0,[z0,z3,z4,z22,z5,z49,z6]),(0,[z0,z3,z4,z22,z5,z6,z74]),(0,[z330,z0,z3,z4,z22,z5,z6]),(0,[z0,z1,z3,z4,z5,z106,z6]),(0,[z0,z9,z3,z4,z5,z6,z375])]],
   [[(0,[z0,z9,z376,z3,z4,z5,z6]),(1,[z0,z3,z4,z45,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z377]),(0,[z29,z0,z3,z4,z22,z5,z6]),(0,[z378,z0,z9,z3,z4,z5,z6]),(0,[z379,z0,z9,z3,z4,z5,z6]),(0,[z380,z0,z9,z3,z4,z5,z6]),(1,[z0,z9,z3,z4,z115,z6])],[(0,[z51,z0,z9,z17,z4,z5,z6]),(0,[z27,z0,z9,z3,z4,z35,z6]),(1,[z0,z9,z3,z4,z381,z6]),(0,[z0,z3,z121,z4,z22,z5,z6]),(1,[z0,z1,z17,z4,z5,z6]),(0,[z37,z0,z9,z4,z5,z93,z6]),(0,[z20,z0,z9,z3,z270,z4,z5]),(0,[z0,z3,z4,z5,z6,z152,z58])],[(0,[z76,z0,z9,z3,z4,z5,z56]),(0,[z0,z9,z4,z137,z15,z5,z6]),(0,[z0,z9,z4,z15,z218,z5,z6]),(0,[z0,z9,z3,z4,z23,z5,z58])],[(0,[z382,z0,z9,z3,z4,z5,z6]),(0,[z383,z0,z9,z3,z4,z5,z6]),(0,[z384,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z16,z6]),(0,[z0,z9,z3,z385,z4,z5,z6]),(0,[z386,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z337,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z387,z6]),(0,[z0,z9,z3,z388,z4,z5,z6])],[(0,[z7,z0,z3,z4,z22,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z389]),(0,[z0,z9,z3,z4,z333,z5,z6]),(0,[z0,z390,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z121,z4,z5,z6])],[(0,[z0,z391,z9,z3,z4,z5,z6]),(0,[z0,z9,z21,z4,z15,z5,z6]),(0,[z0,z9,z392,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z75,z6,z74]),(0,[z393,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z124,z6,z58]),(0,[z0,z9,z3,z4,z5,z394,z6]),(0,[z0,z318,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z152])],[(0,[z0,z9,z3,z4,z5,z6,z395]),(1,[z0,z9,z3,z4,z396,z6]),(0,[z0,z216,z9,z3,z4,z75,z6]),(0,[z85,z0,z9,z17,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z397]),(0,[z398,z0,z9,z3,z4,z5,z6])],[(0,[z399,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z400,z3,z4,z5,z6]),(0,[z0,z144,z9,z4,z15,z5,z6]),(0,[z0,z9,z3,z4,z5,z401,z6]),(0,[z0,z9,z3,z4,z402,z5,z6]),(0,[z38,z0,z9,z3,z4,z5,z106]),(0,[z0,z9,z3,z4,z5,z6,z403])]],
   [[(0,[z0,z9,z404,z3,z4,z5,z6]),(0,[z0,z9,z4,z15,z5,z124,z6]),(0,[z0,z9,z4,z15,z33,z5,z6]),(0,[z0,z9,z405,z3,z4,z5,z6]),(0,[z64,z0,z9,z4,z15,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z406]),(0,[z407,z0,z9,z3,z4,z5,z6])],[(0,[z0,z9,z4,z15,z5,z35,z6]),(0,[z0,z9,z3,z4,z75,z122,z6]),(0,[z0,z1,z3,z4,z122,z5,z6]),(0,[z0,z408,z9,z3,z4,z5,z6])],[(0,[z0,z9,z3,z409,z4,z5,z6]),(0,[z0,z144,z3,z4,z22,z5,z6]),(0,[z410,z0,z9,z3,z4,z5,z6]),(0,[z411,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z412]),(0,[z37,z0,z3,z4,z22,z5,z6]),(0,[z413,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z414,z6]),(0,[z0,z9,z3,z4,z5,z415,z6]),(1,[z0,z9,z3,z4,z5,z237]),(0,[z0,z9,z3,z4,z5,z416,z6]),(0,[z0,z9,z3,z4,z5,z417,z6]),(0,[z0,z9,z418,z3,z4,z5,z6])],[(0,[z64,z0,z3,z4,z22,z5,z6]),(0,[z0,z1,z3,z4,z5,z49,z6]),(0,[z0,z1,z3,z4,z5,z6,z74]),(0,[z38,z0,z3,z4,z5,z6,z39]),(0,[z0,z9,z3,z4,z419,z5,z6]),(0,[z20,z0,z9,z17,z4,z5,z6]),(0,[z12,z0,z420,z3,z4,z5,z6])],[(0,[z0,z9,z3,z4,z5,z421,z6]),(0,[z55,z0,z1,z3,z4,z5,z6]),(0,[z0,z9,z3,z422,z4,z5,z6]),(0,[z0,z9,z423,z3,z4,z5,z6]),(0,[z0,z1,z9,z3,z288,z5,z6]),(0,[z424,z0,z9,z3,z4,z5,z6])],[(0,[z0,z9,z3,z425,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z5,z6]),(0,[z96,z0,z9,z17,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z177])],[(0,[z146,z0,z9,z3,z4,z133,z6]),(0,[z8,z0,z1,z3,z4,z5,z6])],[(0,[z0,z426,z9,z3,z4,z5,z6]),(0,[z0,z9,z53,z4,z5,z93,z6]),(0,[z427,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z17,z4,z5,z16,z6]),(0,[z0,z9,z3,z4,z5,z16,z13]),(0,[z0,z3,z4,z22,z190,z5,z6]),(0,[z0,z3,z91,z4,z22,z5,z6]),(0,[z0,z9,z3,z4,z5,z150,z6]),(0,[z73,z0,z9,z3,z121,z5,z6])]],
   [[(0,[z0,z9,z3,z4,z428,z5,z6]),(0,[z429,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z430,z5,z6]),(0,[z0,z431,z1,z3,z4,z5,z6]),(0,[z0,z9,z17,z121,z4,z5,z6]),(0,[z0,z9,z3,z4,z432,z5,z6])],[(0,[z0,z9,z3,z433,z4,z5,z6]),(0,[z0,z1,z21,z3,z4,z5,z6]),(0,[z434,z0,z9,z3,z4,z5,z6]),(0,[z29,z0,z9,z435,z4,z5,z6]),(0,[z73,z0,z9,z3,z4,z6,z74]),(0,[z0,z9,z3,z4,z5,z436,z6]),(0,[z0,z9,z3,z4,z437,z5,z6]),(0,[z250,z0,z3,z4,z5,z6,z58])],[(0,[z0,z9,z3,z4,z396,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z438]),(0,[z0,z9,z439,z3,z4,z5,z6]),(0,[z0,z1,z1,z3,z4,z5,z6]),(0,[z0,z9,z3,z270,z4,z5,z39]),(0,[z0,z9,z3,z4,z193,z5,z6]),(0,[z440,z0,z9,z3,z4,z5,z6])],[(0,[z441,z0,z9,z3,z4,z5,z6]),(0,[z167,z7,z9,z3,z4,z5,z6]),(0,[z0,z3,z4,z22,z5,z6,z389]),(0,[z0,z9,z3,z4,z5,z442,z6]),(0,[z0,z9,z3,z443,z4,z5,z6])],[(0,[z0,z9,z3,z4,z444,z5,z6]),(0,[z445,z0,z1,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z90,z5,z6]),(0,[z12,z0,z99,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z446]),(0,[z0,z447,z9,z3,z4,z5,z6])],[(0,[z0,z9,z53,z4,z15,z5,z6]),(0,[z73,z0,z9,z3,z4,z122,z6]),(0,[z0,z9,z3,z448,z4,z5,z6])],[(0,[z0,z9,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z449,z5,z6]),(0,[z0,z216,z9,z3,z4,z5,z6]),(0,[z0,z172,z9,z3,z4,z5,z6])],[(0,[z0,z9,z3,z4,z5,z6,z42]),(0,[z0,z9,z3,z4,z450,z5,z6]),(1,[z0,z3,z4,z22,z5,z6]),(0,[z9,z3,z4,z33,z5,z213,z6]),(0,[z0,z9,z3,z4,z5,z6,z451]),(0,[z0,z9,z141,z3,z270,z4,z5])]],
   [[(0,[z452,z0,z9,z3,z4,z5,z6]),(0,[z0,z3,z4,z4,z22,z5,z6]),(0,[z0,z9,z183,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z453]),(0,[z0,z9,z3,z4,z5,z6,z454])],[(0,[z455,z0,z9,z3,z4,z5,z6]),(0,[z456,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z457,z5,z6]),(0,[z0,z9,z458,z3,z4,z5,z6])],[(0,[z51,z0,z9,z348,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z459]),(0,[z0,z9,z3,z460,z4,z5,z6])],[(0,[z76,z0,z9,z3,z4,z381,z6]),(0,[z461,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z462]),(0,[z0,z9,z4,z15,z15,z5,z6])],[(0,[z0,z9,z3,z4,z463,z5,z6]),(0,[z0,z3,z4,z22,z5,z93,z6]),(0,[z0,z159,z9,z3,z4,z5,z6]),(0,[z0,z9,z4,z15,z5,z6,z464])],[(0,[z0,z9,z465,z3,z4,z5,z6]),(1,[z85,z9,z3,z4,z5,z16]),(0,[z0,z9,z3,z4,z5,z6,z39]),(0,[z0,z9,z3,z4,z5,z6,z466]),(0,[z0,z9,z3,z4,z467,z5,z6])],[(0,[z0,z9,z3,z468,z4,z5,z6]),(0,[z0,z9,z3,z469,z4,z5,z6]),(0,[z0,z420,z9,z3,z4,z5,z6])],[(0,[z76,z0,z9,z3,z4,z5,z6]),(0,[z0,z1,z3,z121,z4,z5,z6]),(0,[z470,z0,z9,z3,z4,z5,z6])]],
   [[(0,[z0,z9,z3,z4,z5,z471,z6]),(0,[z0,z9,z3,z472,z4,z5,z6]),(0,[z0,z9,z4,z15,z5,z25,z6]),(0,[z0,z9,z65,z3,z4,z49,z6]),(0,[z0,z9,z3,z4,z5,z6,z473]),(0,[z64,z0,z9,z3,z4,z23,z6])],[(0,[z55,z52,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z474,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z475]),(0,[z0,z9,z3,z476,z4,z5,z6])],[(0,[z0,z9,z3,z4,z75,z5,z6])],[(0,[z0,z477,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z10,z5,z6]),(0,[z478,z0,z9,z3,z4,z5,z6]),(1,[z0,z17,z4,z22,z5,z6]),(1,[z0,z9,z100,z4,z5,z6]),(0,[z0,z9,z131,z3,z4,z5,z6])],[(0,[z146,z0,z9,z3,z4,z5,z6]),(0,[z43,z9,z3,z4,z5,z6,z56]),(0,[z0,z3,z294,z4,z22,z5,z6]),(0,[z12,z0,z1,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z479,z5,z6])],[(0,[z0,z216,z9,z4,z15,z5,z6]),(0,[z38,z0,z159,z3,z4,z5,z6]),(0,[z0,z9,z217,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z226,z5,z6]),(0,[z0,z9,z3,z4,z480,z5,z6]),(0,[z481,z0,z9,z3,z4,z5,z6])],[(0,[z37,z0,z9,z4,z5,z49,z6]),(0,[z482,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z483,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z484]),(0,[z0,z9,z3,z4,z5,z58,z13])]],
   [[(0,[z215,z0,z9,z3,z4,z5,z6]),(0,[z52,z9,z3,z53,z4,z5,z6]),(0,[z20,z0,z62,z9,z4,z5,z6]),(1,[z0,z9,z435,z4,z5,z6]),(0,[z0,z216,z3,z4,z22,z5,z6]),(0,[z38,z0,z1,z3,z4,z5,z6]),(0,[z455,z0,z9,z4,z15,z5,z6]),(0,[z456,z0,z9,z4,z15,z5,z6]),(0,[z0,z9,z3,z4,z122,z6,z58]),(0,[z0,z9,z367,z3,z4,z5,z6])],[(0,[z0,z9,z3,z4,z5,z485,z6]),(0,[z0,z9,z17,z4,z5,z6,z39])],[(0,[z167,z0,z3,z4,z22,z5,z6]),(0,[z0,z9,z3,z486,z4,z5,z6])],[(0,[z55,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z487]),(0,[z0,z9,z3,z4,z5,z488,z6]),(0,[z0,z9,z3,z489,z4,z5,z6]),(0,[z0,z9,z3,z490,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z491]),(0,[z0,z159,z9,z4,z15,z5,z6]),(0,[z0,z9,z17,z17,z4,z5,z6]),(0,[z0,z9,z3,z270,z4,z5,z25])],[(0,[z64,z0,z9,z3,z4,z75,z6]),(0,[z0,z492,z9,z3,z4,z5,z6]),(1,[z0,z62,z206,z4,z5,z6]),(0,[z0,z493,z9,z3,z4,z5,z6]),(0,[z0,z3,z4,z402,z22,z5,z6]),(0,[z0,z3,z4,z22,z5,z6,z39]),(0,[z0,z9,z3,z4,z5,z494,z6])],[(0,[z8,z0,z9,z3,z4,z5,z6]),(0,[z495,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z121,z122,z5,z6])],[(0,[z0,z9,z17,z4,z75,z5,z6]),(0,[z76,z0,z9,z4,z15,z5,z6]),(0,[z0,z9,z3,z4,z496,z5,z6]),(0,[z0,z159,z3,z4,z22,z5,z6]),(0,[z0,z1,z216,z3,z4,z5,z6]),(0,[z0,z9,z3,z497,z4,z5,z6]),(0,[z73,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z498,z4,z5,z6])],[(0,[z0,z9,z17,z4,z10,z5,z6]),(0,[z499,z0,z9,z3,z4,z5,z6]),(0,[z0,z500,z9,z3,z4,z5,z6]),(0,[z273,z0,z9,z3,z4,z5,z6]),(0,[z501,z0,z9,z3,z4,z5,z6])]],
   [[(0,[z502,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z503,z6])],[(0,[z0,z3,z4,z22,z75,z5,z6]),(0,[z0,z9,z3,z504,z4,z5,z6]),(0,[z76,z0,z3,z4,z22,z5,z6]),(0,[z0,z9,z3,z4,z374,z5,z6]),(0,[z0,z9,z3,z505,z4,z5,z6]),(0,[z0,z9,z3,z506,z4,z5,z6]),(1,[z73,z0,z9,z3,z6,z74])],[(0,[z0,z9,z2,z3,z4,z5,z6]),(0,[z0,z9,z32,z4,z15,z5,z6]),(0,[z64,z0,z9,z3,z4,z33,z6]),(0,[z37,z0,z9,z3,z4,z6,z58]),(0,[z37,z64,z0,z9,z3,z4,z6]),(0,[z0,z9,z3,z4,z6,z58,z74])],[(0,[z507,z0,z9,z3,z4,z5,z6]),(0,[z146,z0,z9,z4,z15,z5,z6]),(0,[z0,z9,z435,z3,z4,z5,z6]),(0,[z445,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z508]),(0,[z0,z9,z3,z509,z4,z5,z6]),(0,[z19,z0,z9,z17,z4,z5,z6]),(0,[z0,z9,z24,z17,z4,z5,z6]),(0,[z0,z9,z3,z4,z510,z5,z6]),(0,[z0,z334,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z511]),(0,[z0,z9,z3,z4,z5,z198,z6])],[(0,[z27,z0,z9,z17,z4,z5,z6]),(0,[z512,z0,z9,z3,z4,z5,z6])],[(0,[z8,z0,z9,z3,z4,z5,z157]),(0,[z0,z9,z3,z4,z513,z5,z6]),(0,[z0,z9,z3,z514,z4,z5,z6]),(0,[z0,z1,z206,z3,z4,z5,z6]),(0,[z0,z9,z183,z288,z4,z5,z6]),(0,[z0,z9,z4,z15,z5,z6,z112])],[(0,[z146,z0,z3,z4,z22,z5,z6]),(0,[z0,z3,z4,z22,z5,z106,z6]),(1,[z0,z9,z3,z4,z174,z6]),(0,[z515,z0,z9,z3,z4,z5,z6])],[(0,[z0,z9,z3,z4,z33,z5,z6]),(0,[z0,z216,z3,z4,z33,z5,z6]),(0,[z12,z0,z9,z3,z4,z5,z25]),(0,[z0,z9,z516,z3,z4,z5,z6])]],
   [[(0,[z43,z0,z1,z3,z4,z5,z6]),(0,[z0,z62,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z39]),(0,[z0,z9,z3,z4,z5,z6,z517]),(0,[z518,z0,z9,z3,z4,z5,z6])],[(1,[z0,z9,z348,z4,z5,z6]),(0,[z0,z9,z194,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z519,z5,z6]),(0,[z0,z9,z4,z10,z15,z5,z6]),(0,[z0,z1,z3,z44,z4,z5,z6]),(0,[z0,z9,z4,z15,z5,z6,z56]),(0,[z85,z0,z9,z36,z4,z5,z6]),(0,[z0,z9,z520,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z521])],[(0,[z55,z0,z9,z4,z15,z5,z6]),(0,[z52,z0,z1,z3,z4,z5,z6]),(0,[z522,z0,z9,z3,z4,z5,z6]),(0,[z0,z523,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z524,z5,z6]),(0,[z0,z9,z3,z270,z4,z5,z106])],[(0,[z43,z0,z9,z3,z10,z5,z6]),(1,[z0,z9,z269,z4,z5,z6]),(0,[z0,z9,z4,z22,z15,z5,z6]),(0,[z0,z9,z131,z91,z4,z5,z6])],[(0,[z8,z0,z9,z4,z15,z5,z6]),(0,[z0,z9,z3,z525,z4,z5,z6]),(0,[z0,z9,z3,z526,z4,z5,z6]),(0,[z0,z79,z1,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z527,z5,z6]),(0,[z0,z9,z17,z3,z294,z5,z6]),(0,[z528,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z529,z5,z6])],[(0,[z0,z1,z3,z4,z75,z5,z6]),(0,[z83,z0,z1,z3,z4,z5,z6]),(0,[z73,z0,z9,z4,z15,z5,z6]),(0,[z0,z9,z65,z3,z4,z5,z6]),(0,[z73,z0,z9,z3,z4,z5,z31])],[(0,[z146,z144,z9,z3,z4,z5,z6]),(0,[z0,z1,z3,z294,z4,z5,z6]),(0,[z0,z9,z4,z15,z148,z5,z6]),(0,[z0,z9,z3,z530,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z174,z6])],[(0,[z0,z9,z531,z3,z4,z5,z6]),(1,[z0,z9,z3,z4,z129,z6]),(0,[z8,z0,z3,z4,z22,z5,z6]),(0,[z0,z9,z3,z4,z5,z532,z6]),(0,[z94,z9,z3,z4,z33,z5,z6]),(0,[z0,z9,z17,z4,z510,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z533])]],
   [[(0,[z51,z9,z3,z4,z5,z35,z6]),(0,[z146,z0,z2,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z534,z6]),(0,[z0,z9,z3,z4,z5,z6,z535]),(0,[z0,z9,z536,z3,z4,z5,z6]),(1,[z0,z9,z3,z4,z77,z6]),(0,[z73,z0,z3,z4,z22,z5,z6]),(0,[z0,z537,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z23,z5,z6])],[(0,[z51,z0,z1,z3,z4,z5,z6]),(0,[z0,z9,z2,z4,z15,z5,z6]),(0,[z538,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z539,z4,z5,z6]),(0,[z302,z0,z9,z17,z4,z5,z6]),(0,[z0,z540,z9,z3,z4,z5,z6]),(1,[z223,z0,z9,z4,z5,z6])],[(0,[z0,z541,z9,z3,z4,z5,z6]),(0,[z542,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z543,z4,z5,z6]),(0,[z87,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z18,z6])],[(0,[z0,z9,z3,z4,z5,z544,z6]),(0,[z0,z9,z336,z3,z4,z5,z6]),(0,[z0,z9,z3,z545,z4,z5,z6]),(0,[z29,z0,z9,z3,z288,z5,z6]),(0,[z27,z0,z9,z3,z4,z124,z6]),(0,[z546,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z547,z5,z6]),(0,[z12,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z270,z4,z5,z13])],[(0,[z0,z9,z3,z4,z258,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z34]),(0,[z0,z9,z3,z548,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z549,z6]),(0,[z0,z9,z3,z4,z5,z6,z550]),(0,[z0,z551,z9,z3,z4,z5,z6])],[(0,[z0,z9,z3,z4,z5,z552,z6])],[(0,[z85,z0,z1,z3,z4,z5,z6]),(0,[z118,z0,z1,z3,z4,z5,z6]),(1,[z0,z3,z4,z66,z5,z6])],[(0,[z0,z9,z553,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z381,z5,z6]),(0,[z38,z0,z9,z3,z4,z5,z6]),(0,[z314,z0,z9,z17,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z58])]],
   [[(0,[z0,z9,z3,z4,z554,z5,z6]),(0,[z0,z126,z1,z3,z4,z5,z6]),(1,[z0,z9,z4,z333,z5,z6])],[(0,[z555,z0,z9,z3,z4,z5,z6]),(0,[z302,z0,z196,z3,z4,z5,z6]),(0,[z0,z81,z3,z121,z4,z5,z6])],[(0,[z0,z556,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z56,z13]),(0,[z0,z557,z9,z3,z4,z5,z6])],[(1,[z173,z0,z9,z3,z4,z6]),(0,[z558,z0,z9,z3,z4,z5,z6])],[(0,[z0,z559,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z560]),(0,[z29,z0,z9,z17,z4,z5,z6]),(1,[z0,z9,z3,z4,z254,z6]),(0,[z0,z9,z65,z4,z15,z5,z6]),(0,[z0,z9,z17,z4,z23,z5,z6])],[(0,[z0,z9,z3,z14,z4,z5,z6]),(0,[z96,z0,z1,z3,z4,z5,z6]),(0,[z561,z0,z9,z3,z4,z5,z6]),(0,[z27,z0,z216,z3,z4,z5,z6]),(0,[z64,z0,z9,z3,z270,z4,z5])],[(0,[z0,z9,z3,z4,z5,z562,z6]),(0,[z0,z9,z3,z4,z35,z6,z74]),(0,[z0,z9,z3,z563,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z13])],[(0,[z0,z21,z3,z4,z22,z5,z6]),(0,[z0,z216,z9,z3,z4,z33,z6]),(0,[z0,z9,z3,z4,z5,z564,z6]),(0,[z0,z9,z3,z4,z5,z285,z6]),(1,[z0,z9,z3,z4,z5,z186]),(0,[z12,z0,z9,z3,z4,z5,z13])]],
   [[(0,[z0,z9,z3,z565,z4,z5,z6]),(0,[z7,z0,z9,z17,z4,z5,z6]),(0,[z0,z206,z3,z4,z22,z5,z6]),(0,[z0,z9,z3,z4,z158,z5,z6]),(0,[z341,z0,z9,z17,z4,z5,z6]),(1,[z0,z9,z65,z4,z218,z6]),(1,[z0,z99,z3,z4,z5,z6]),(0,[z12,z0,z9,z3,z91,z5,z6])],[(0,[z0,z9,z3,z4,z566,z5,z6]),(0,[z567,z0,z9,z3,z4,z5,z6]),(0,[z568,z0,z9,z3,z4,z5,z6]),(1,[z0,z9,z4,z5,z6,z177]),(0,[z0,z9,z147,z17,z4,z5,z6])],[(0,[z0,z9,z3,z36,z4,z5,z6]),(0,[z0,z1,z159,z3,z4,z5,z6]),(0,[z0,z9,z569,z3,z4,z5,z6]),(0,[z302,z0,z9,z3,z294,z5,z6]),(0,[z12,z0,z9,z4,z15,z5,z6]),(0,[z0,z9,z65,z3,z4,z218,z6]),(0,[z12,z0,z9,z3,z5,z6,z13]),(0,[z0,z9,z3,z4,z570,z5,z6]),(0,[z0,z9,z91,z4,z570,z5,z6])],[(0,[z0,z9,z3,z571,z4,z5,z6]),(0,[z572,z0,z9,z3,z4,z5,z6]),(0,[z573,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z17,z4,z5,z6,z58]),(1,[z0,z9,z4,z570,z5,z6]),(0,[z0,z9,z3,z4,z574,z5,z6])],[(0,[z0,z3,z53,z4,z22,z5,z6]),(0,[z0,z9,z21,z17,z4,z5,z6]),(0,[z0,z9,z3,z4,z575,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z576]),(0,[z0,z9,z3,z4,z5,z25,z58])],[(0,[z8,z0,z9,z245,z4,z5,z6]),(0,[z0,z3,z4,z22,z5,z16,z6]),(0,[z0,z9,z3,z4,z5,z6,z577]),(0,[z0,z578,z1,z3,z4,z5,z6]),(0,[z302,z0,z579,z3,z4,z5,z6]),(0,[z0,z9,z3,z580,z4,z5,z6]),(0,[z581,z0,z9,z3,z4,z5,z6])],[(0,[z0,z144,z9,z17,z4,z5,z6]),(0,[z582,z0,z9,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z358]),(0,[z0,z9,z583,z3,z4,z5,z6]),(0,[z38,z0,z9,z4,z15,z5,z6]),(0,[z37,z0,z9,z17,z4,z5,z6]),(1,[z0,z9,z3,z222,z4,z5])],[(0,[z43,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z584,z5,z6]),(0,[z85,z0,z9,z372,z4,z5,z6]),(0,[z165,z0,z9,z3,z4,z5,z6]),(0,[z0,z579,z9,z3,z4,z5,z6]),(0,[z64,z0,z9,z17,z4,z5,z6]),(0,[z585,z0,z9,z3,z4,z5,z6])]],
   [[(1,[z287,z0,z3,z4,z5,z6]),(0,[z586,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z4,z15,z5,z93,z6]),(0,[z0,z587,z9,z3,z4,z5,z6])],[(0,[z588,z0,z9,z3,z4,z5,z6]),(0,[z0,z589,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z590]),(0,[z52,z0,z9,z3,z4,z5,z6]),(0,[z38,z0,z3,z4,z22,z5,z6]),(0,[z73,z332,z9,z3,z4,z5,z6]),(0,[z0,z9,z162,z121,z4,z5,z6])],[(0,[z8,z0,z336,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z591,z6]),(0,[z0,z9,z17,z4,z5,z6,z13])],[(0,[z0,z62,z206,z3,z4,z5,z6]),(0,[z0,z65,z3,z4,z22,z5,z6]),(0,[z73,z0,z9,z335,z4,z5,z6])],[(0,[z0,z9,z3,z4,z122,z35,z6]),(0,[z0,z9,z3,z4,z75,z6,z58]),(0,[z0,z9,z3,z4,z5,z592,z6]),(1,[z94,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z593]),(0,[z594,z0,z9,z3,z4,z5,z6])],[(0,[z0,z9,z3,z4,z5,z595,z6]),(0,[z0,z1,z9,z3,z22,z5,z6]),(0,[z0,z9,z3,z596,z4,z5,z6]),(0,[z0,z9,z597,z3,z4,z5,z6])],[(0,[z55,z0,z9,z3,z4,z75,z6])],[(0,[z0,z9,z598,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z292,z5,z6]),(0,[z0,z9,z3,z4,z5,z599,z6])]],
   [[(0,[z600,z0,z9,z3,z4,z5,z6]),(0,[z601,z0,z9,z3,z4,z5,z6]),(1,[z0,z159,z3,z4,z5,z106]),(0,[z20,z0,z9,z4,z218,z5,z6])],[(0,[z0,z1,z3,z4,z5,z16,z6]),(0,[z602,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z603,z3,z4,z5,z6]),(0,[z27,z0,z3,z4,z5,z106,z6]),(0,[z0,z9,z3,z604,z4,z5,z6])],[(0,[z0,z9,z3,z4,z605,z5,z6]),(0,[z0,z9,z121,z4,z161,z5,z6])],[(0,[z0,z9,z3,z4,z5,z606,z6]),(0,[z0,z9,z3,z4,z5,z6,z607]),(0,[z608,z0,z9,z3,z4,z5,z6]),(0,[z567,z0,z3,z4,z22,z5,z6]),(1,[z0,z9,z17,z4,z5,z6])],[(0,[z609,z0,z9,z3,z4,z5,z6]),(0,[z51,z0,z206,z3,z4,z5,z6])],[(0,[z0,z9,z3,z610,z4,z5,z6]),(0,[z0,z9,z3,z4,z611,z5,z6]),(0,[z0,z9,z612,z3,z4,z5,z6]),(1,[z0,z3,z4,z179,z5,z6])],[(0,[z0,z9,z3,z4,z613,z5,z6]),(0,[z43,z0,z9,z4,z15,z5,z6]),(0,[z614,z0,z9,z3,z4,z5,z6]),(0,[z0,z62,z9,z4,z15,z5,z6])],[(0,[z64,z0,z9,z3,z4,z35,z6]),(0,[z0,z9,z3,z4,z5,z6,z615]),(0,[z0,z9,z4,z268,z15,z5,z6]),(0,[z616,z0,z9,z3,z4,z5,z6])]],
   [[(0,[z146,z0,z9,z3,z4,z396,z6]),(1,[z0,z9,z3,z4,z259,z6]),(0,[z52,z0,z9,z4,z15,z5,z6]),(0,[z0,z62,z9,z206,z4,z5,z6]),(0,[z0,z9,z617,z3,z4,z5,z6]),(0,[z38,z0,z3,z4,z33,z5,z6])],[(0,[z618,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z44,z4,z15,z5,z6]),(0,[z619,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z620,z5,z6])],[(0,[z0,z9,z3,z4,z621,z5,z6]),(0,[z0,z9,z3,z53,z4,z5,z6]),(0,[z622,z0,z9,z3,z4,z5,z6]),(0,[z12,z318,z9,z3,z4,z5,z6])],[(0,[z0,z9,z3,z4,z5,z623,z6]),(1,[z43,z9,z3,z44,z5,z6]),(0,[z624,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z22,z5,z6]),(0,[z0,z9,z3,z625,z4,z5,z6]),(1,[z0,z196,z3,z4,z5,z6]),(0,[z0,z9,z17,z4,z5,z599,z6]),(0,[z231,z0,z9,z17,z4,z5,z6]),(0,[z0,z9,z3,z626,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z627,z6])],[(0,[z0,z9,z3,z4,z628,z5,z6]),(0,[z0,z9,z3,z4,z629,z5,z6]),(0,[z630,z0,z9,z3,z4,z5,z6]),(0,[z96,z0,z9,z3,z4,z5,z6]),(0,[z631,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z632]),(0,[z0,z633,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z634,z4,z5,z6]),(0,[z0,z279,z9,z3,z4,z5,z6])],[(0,[z0,z9,z135,z3,z4,z5,z6]),(0,[z0,z635,z9,z3,z4,z5,z6]),(0,[z452,z0,z3,z4,z22,z5,z6]),(0,[z0,z9,z3,z636,z4,z5,z6])],[(0,[z0,z62,z9,z32,z4,z5,z6]),(0,[z637,z0,z9,z3,z4,z5,z6]),(1,[z0,z9,z17,z15,z5,z6]),(0,[z0,z9,z3,z222,z4,z218,z5])],[(0,[z0,z3,z270,z4,z22,z5,z6]),(0,[z0,z638,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z639,z5,z6]),(0,[z20,z0,z9,z3,z4,z5,z58])]],
   [[(0,[z0,z9,z3,z4,z5,z259,z6]),(0,[z0,z9,z3,z4,z640,z5,z6]),(0,[z641,z0,z9,z3,z4,z5,z6]),(0,[z642,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z643,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z50]),(0,[z0,z9,z3,z4,z161,z5,z6])],[(1,[z0,z9,z372,z4,z5,z6]),(0,[z644,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z241,z3,z4,z5,z6]),(0,[z0,z1,z583,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z645,z6]),(0,[z37,z0,z9,z65,z4,z5,z6]),(0,[z0,z9,z3,z646,z4,z5,z6]),(0,[z0,z9,z3,z4,z647,z5,z6]),(1,[z0,z9,z286,z4,z5,z6]),(0,[z0,z9,z3,z648,z4,z5,z6])],[(0,[z167,z9,z3,z4,z5,z35,z6]),(0,[z0,z649,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z650,z4,z5,z6]),(0,[z0,z431,z9,z3,z4,z5,z6]),(0,[z651,z0,z9,z3,z4,z5,z6]),(0,[z38,z0,z9,z3,z4,z331,z6]),(0,[z0,z9,z4,z15,z5,z106,z6]),(0,[z0,z3,z294,z4,z179,z5,z6])],[(0,[z52,z144,z9,z3,z4,z5,z6]),(0,[z0,z3,z121,z4,z66,z5,z6])],[(0,[z652,z0,z9,z3,z4,z5,z6]),(0,[z85,z0,z9,z4,z15,z5,z6]),(0,[z0,z578,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z653,z6]),(0,[z0,z1,z9,z3,z4,z5,z6]),(0,[z27,z0,z1,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z654,z6]),(0,[z0,z216,z9,z17,z4,z5,z6]),(0,[z0,z9,z3,z4,z254,z5,z6]),(0,[z0,z9,z4,z366,z15,z5,z6]),(0,[z655,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z218,z5,z6]),(0,[z173,z0,z9,z3,z4,z93,z6]),(0,[z353,z0,z9,z3,z4,z5,z6])],[(0,[z0,z9,z44,z4,z54,z5,z6]),(0,[z0,z9,z3,z4,z5,z25,z56])],[(0,[z0,z9,z17,z53,z4,z5,z6]),(0,[z167,z0,z9,z17,z4,z5,z6]),(0,[z0,z9,z656,z3,z4,z5,z6]),(0,[z616,z0,z9,z4,z15,z5,z6]),(0,[z0,z9,z3,z270,z4,z23,z5])],[(0,[z0,z9,z3,z4,z657,z5,z6]),(0,[z0,z9,z17,z4,z22,z5,z6]),(0,[z0,z9,z288,z4,z15,z5,z6]),(1,[z0,z579,z3,z4,z5,z6]),(0,[z12,z353,z9,z3,z4,z5,z6]),(1,[z0,z9,z4,z5,z198,z6])]],
   [[(0,[z658,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z659,z3,z4,z5,z6]),(0,[z0,z3,z4,z10,z22,z5,z6]),(0,[z0,z9,z3,z4,z660,z5,z6]),(0,[z0,z9,z206,z17,z4,z5,z6]),(0,[z661,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z286,z3,z4,z5,z6]),(0,[z64,z0,z9,z3,z270,z4,z6])],[(0,[z0,z9,z3,z4,z5,z6,z662]),(0,[z0,z9,z3,z4,z218,z5,z237])],[(1,[z51,z2,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z663,z5,z6]),(0,[z0,z206,z3,z32,z4,z5,z6]),(0,[z0,z9,z3,z664,z4,z5,z6]),(0,[z0,z3,z4,z22,z22,z5,z6]),(0,[z0,z9,z3,z4,z5,z124,z6]),(0,[z0,z159,z9,z17,z4,z5,z6]),(1,[z0,z9,z367,z4,z5,z6]),(0,[z0,z9,z3,z270,z4,z5,z6])],[(0,[z0,z9,z269,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z35,z6]),(0,[z96,z0,z9,z4,z15,z5,z6])],[(0,[z0,z9,z3,z4,z5,z665,z6]),(0,[z666,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z667,z5,z6]),(0,[z0,z9,z4,z15,z122,z5,z6]),(0,[z0,z9,z17,z4,z5,z6,z50]),(0,[z0,z9,z3,z668,z4,z5,z6])],[(0,[z76,z0,z9,z17,z4,z5,z6]),(0,[z96,z0,z9,z206,z4,z5,z6]),(0,[z0,z9,z3,z4,z669,z5,z6])],[(0,[z0,z9,z3,z3,z4,z5,z6]),(0,[z7,z9,z3,z53,z4,z5,z6]),(0,[z631,z0,z3,z4,z22,z5,z6]),(0,[z0,z9,z3,z4,z5,z59,z6]),(0,[z0,z9,z670,z3,z4,z5,z6]),(0,[z0,z9,z4,z15,z5,z6,z74]),(0,[z0,z9,z4,z15,z5,z49,z6])],[(0,[z0,z9,z3,z4,z671,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z672]),(1,[z0,z204,z3,z4,z5,z6]),(0,[z0,z9,z673,z3,z4,z5,z6]),(0,[z0,z9,z3,z674,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z675])]],
   [[(0,[z55,z0,z3,z4,z22,z5,z6]),(0,[z0,z1,z612,z3,z4,z5,z6]),(0,[z0,z9,z17,z4,z218,z5,z6]),(1,[z0,z9,z3,z91,z5,z25])],[(0,[z0,z1,z3,z4,z10,z5,z6]),(0,[z0,z9,z3,z4,z5,z676,z6]),(0,[z302,z0,z1,z3,z4,z5,z6]),(0,[z332,z0,z9,z3,z4,z5,z6])],[(0,[z146,z0,z9,z17,z4,z5,z6]),(0,[z0,z9,z3,z4,z4,z5,z6]),(0,[z85,z0,z9,z3,z4,z5,z16]),(0,[z677,z0,z9,z3,z4,z5,z6]),(0,[z27,z0,z9,z3,z4,z5,z150]),(0,[z0,z9,z678,z3,z4,z5,z6])],[(0,[z96,z0,z9,z32,z4,z5,z6]),(0,[z679,z0,z9,z3,z4,z5,z6]),(0,[z0,z3,z4,z444,z22,z5,z6]),(0,[z0,z3,z4,z22,z218,z5,z6]),(0,[z0,z1,z9,z4,z15,z5,z6]),(0,[z0,z578,z9,z4,z15,z5,z6]),(0,[z0,z9,z141,z3,z4,z5,z93]),(0,[z0,z130,z9,z3,z4,z5,z6])],[(0,[z0,z216,z9,z3,z4,z35,z6]),(0,[z0,z9,z3,z4,z680,z5,z6]),(1,[z20,z0,z9,z4,z5,z50])],[(0,[z681,z0,z9,z3,z4,z5,z6]),(0,[z8,z0,z9,z3,z44,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z6]),(0,[z0,z9,z682,z3,z4,z5,z6]),(0,[z0,z9,z141,z3,z4,z5,z58]),(0,[z0,z9,z3,z683,z4,z5,z6])],[(0,[z0,z9,z3,z4,z684,z5,z6]),(0,[z0,z1,z3,z4,z22,z5,z6]),(0,[z0,z9,z17,z4,z5,z124,z6]),(0,[z0,z9,z17,z4,z33,z5,z6]),(0,[z0,z9,z3,z4,z685,z5,z6]),(0,[z0,z9,z17,z270,z4,z5,z6]),(0,[z0,z9,z686,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z687,z5,z6])],[(0,[z688,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z17,z4,z5,z35,z6]),(0,[z689,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z690]),(0,[z314,z0,z1,z3,z4,z5,z6]),(0,[z40,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z691,z6])]],
   [[(0,[z0,z9,z692,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z693]),(1,[z0,z151,z3,z4,z5,z6])],[(0,[z694,z0,z9,z3,z4,z5,z6]),(0,[z9,z21,z3,z53,z4,z5,z6]),(0,[z0,z3,z4,z22,z33,z5,z6]),(0,[z695,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z696,z5,z6])],[(0,[z0,z9,z3,z4,z5,z697,z6]),(0,[z287,z0,z9,z3,z4,z5,z6]),(0,[z0,z3,z4,z22,z5,z35,z6]),(0,[z0,z9,z3,z698,z4,z5,z6]),(0,[z0,z9,z17,z3,z4,z5,z6]),(1,[z0,z420,z3,z4,z5,z6]),(0,[z0,z9,z3,z91,z4,z5,z25])],[(0,[z699,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z77,z6]),(0,[z85,z0,z9,z3,z4,z5,z56]),(0,[z700,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z63,z6]),(0,[z0,z9,z3,z105,z4,z5,z6]),(0,[z273,z0,z9,z4,z5,z6,z39])],[(0,[z0,z2,z3,z4,z22,z5,z6]),(0,[z52,z0,z9,z3,z4,z75,z6]),(0,[z29,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z22,z5,z6]),(0,[z73,z0,z9,z17,z4,z5,z6])],[(0,[z0,z225,z3,z44,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z326,z6]),(0,[z0,z9,z3,z4,z15,z5,z6]),(0,[z0,z9,z3,z60,z4,z5,z6]),(0,[z0,z701,z9,z3,z4,z5,z6])],[(0,[z51,z0,z9,z135,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z702,z6]),(0,[z20,z0,z1,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z464]),(0,[z0,z9,z17,z4,z4,z5,z6])],[(0,[z0,z9,z3,z703,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z704,z6]),(0,[z0,z17,z3,z4,z22,z5,z6]),(0,[z0,z241,z3,z4,z22,z5,z6]),(0,[z0,z1,z3,z4,z218,z5,z6]),(0,[z0,z9,z3,z4,z705,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z706])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z707,z0,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z708,z6]),(0,[z9,z3,z4,z5,z6,z709]),(0,[z0,z1,z3,z554,z5,z6]),(0,[z0,z4,z22,z570,z5,z6]),(0,[z0,z710,z3,z4,z5,z6]),(0,[z711,z1,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z342,z58])],[(0,[z0,z9,z3,z4,z331,z106]),(0,[z64,z0,z9,z17,z270,z4])],[(0,[z43,z9,z3,z44,z5,z6]),(0,[z0,z84,z4,z15,z5,z6]),(0,[z0,z84,z3,z4,z5,z31]),(0,[z0,z9,z3,z5,z6,z712]),(0,[z353,z9,z367,z4,z5,z6])],[(0,[z0,z9,z17,z128,z5,z6]),(0,[z0,z9,z3,z4,z713,z5]),(0,[z0,z9,z714,z4,z5,z6]),(0,[z0,z3,z460,z22,z5,z6]),(0,[z0,z3,z4,z715,z5,z6]),(0,[z0,z9,z716,z4,z5,z6]),(0,[z37,z47,z9,z4,z49,z6]),(0,[z73,z0,z9,z3,z6,z712]),(0,[z0,z279,z4,z570,z5,z6]),(0,[z0,z9,z4,z23,z198,z58])],[(0,[z146,z144,z3,z4,z5,z6]),(0,[z0,z717,z3,z4,z5,z6])],[(0,[z0,z3,z22,z92,z5,z6]),(0,[z0,z9,z17,z664,z5,z6]),(0,[z0,z183,z4,z22,z5,z6]),(0,[z94,z3,z4,z22,z5,z6]),(0,[z0,z9,z3,z4,z5,z150]),(0,[z0,z9,z17,z15,z5,z6]),(0,[z318,z420,z3,z4,z5,z6])],[(0,[z0,z718,z3,z4,z5,z6]),(0,[z0,z1,z4,z15,z5,z6]),(0,[z0,z1,z3,z4,z5,z31]),(0,[z0,z159,z4,z15,z5,z106]),(0,[z0,z172,z241,z4,z5,z6]),(0,[z719,z0,z9,z3,z4,z6]),(0,[z0,z9,z3,z4,z720,z6])],[(0,[z0,z9,z3,z4,z5,z721]),(1,[z722,z3,z4,z5,z6]),(0,[z644,z9,z21,z4,z5,z6]),(0,[z0,z723,z3,z4,z5,z6]),(0,[z0,z241,z4,z444,z5,z6]),(0,[z0,z1,z17,z294,z5,z6]),(0,[z0,z724,z3,z4,z5,z6]),(0,[z0,z9,z476,z15,z5,z6]),(0,[z0,z725,z3,z4,z5,z6]),(0,[z332,z151,z3,z4,z5,z6]),(0,[z0,z726,z3,z4,z5,z6])]],
   [[(0,[z0,z9,z3,z727,z5,z6]),(0,[z0,z9,z4,z728,z5,z6]),(0,[z0,z9,z3,z4,z729,z6]),(0,[z0,z9,z372,z4,z5,z6]),(0,[z0,z730,z3,z4,z5,z6]),(0,[z731,z9,z3,z4,z5,z6]),(0,[z38,z0,z3,z4,z5,z358]),(0,[z732,z9,z3,z4,z5,z6]),(0,[z64,z0,z9,z3,z472,z4]),(0,[z0,z9,z286,z4,z5,z6]),(0,[z0,z9,z162,z4,z5,z6]),(0,[z0,z9,z4,z161,z5,z6]),(0,[z733,z9,z3,z4,z5,z6])],[(0,[z0,z9,z734,z4,z5,z6]),(0,[z735,z0,z9,z4,z15,z6]),(0,[z0,z9,z17,z736,z4,z5])],[(0,[z287,z3,z4,z5,z35,z6]),(0,[z0,z3,z474,z22,z5,z6]),(0,[z637,z9,z3,z4,z35,z6]),(0,[z567,z0,z4,z148,z5,z6]),(0,[z0,z9,z3,z4,z737,z6]),(0,[z0,z9,z738,z4,z5,z6]),(0,[z0,z9,z739,z4,z5,z6])],[(0,[z0,z9,z3,z4,z740,z6]),(0,[z0,z9,z4,z5,z6,z741]),(0,[z0,z9,z742,z4,z5,z6])],[(0,[z0,z743,z3,z4,z5,z6]),(0,[z744,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z122,z31])],[(0,[z0,z9,z3,z4,z745,z6]),(0,[z0,z9,z746,z4,z5,z6]),(0,[z0,z9,z747,z4,z5,z6]),(0,[z130,z9,z4,z15,z5,z6]),(0,[z130,z9,z3,z4,z5,z31])],[(0,[z0,z748,z3,z4,z5,z6]),(0,[z0,z749,z3,z4,z5,z6]),(0,[z750,z0,z9,z4,z15,z5]),(0,[z0,z9,z4,z15,z751,z6]),(0,[z341,z9,z147,z4,z5,z6]),(0,[z0,z9,z3,z4,z752,z6]),(0,[z318,z99,z3,z4,z5,z6]),(0,[z0,z9,z4,z753,z5,z6])],[(0,[z0,z9,z3,z4,z754,z6]),(0,[z0,z755,z3,z4,z5,z6]),(0,[z247,z0,z3,z4,z5,z389]),(0,[z756,z0,z9,z4,z5,z6]),(0,[z0,z9,z65,z222,z4,z218]),(0,[z0,z420,z3,z4,z174,z6])]],
   [[(0,[z0,z3,z4,z757,z5,z6]),(0,[z0,z758,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z759,z6]),(0,[z0,z131,z4,z22,z5,z6]),(0,[z0,z3,z4,z158,z5,z106]),(0,[z445,z0,z3,z4,z5,z358]),(0,[z0,z9,z3,z4,z760,z6])],[(0,[z51,z2,z3,z4,z5,z6]),(0,[z8,z336,z3,z10,z5,z6]),(0,[z0,z3,z4,z22,z259,z6]),(0,[z0,z3,z4,z22,z751,z6]),(0,[z0,z1,z3,z4,z6,z120]),(0,[z0,z9,z4,z761,z5,z6]),(0,[z0,z762,z3,z4,z5,z6])],[(0,[z0,z336,z14,z4,z5,z6]),(0,[z43,z9,z44,z15,z5,z6]),(0,[z0,z1,z4,z54,z5,z6]),(0,[z85,z9,z17,z4,z5,z16]),(0,[z0,z9,z3,z4,z5,z763]),(0,[z0,z9,z764,z4,z5,z6]),(0,[z9,z765,z3,z4,z5,z6]),(0,[z0,z766,z3,z4,z5,z6]),(0,[z0,z767,z3,z4,z5,z6]),(0,[z353,z420,z3,z4,z5,z6])],[(0,[z0,z9,z768,z4,z5,z6]),(0,[z146,z144,z4,z15,z5,z6]),(0,[z0,z9,z245,z4,z5,z42]),(0,[z769,z9,z3,z4,z5,z6]),(0,[z0,z9,z4,z5,z198,z237]),(0,[z0,z9,z3,z270,z4,z238]),(0,[z0,z9,z335,z4,z5,z186])],[(0,[z0,z1,z770,z4,z5,z6]),(0,[z0,z9,z4,z15,z5,z150]),(0,[z0,z9,z3,z771,z5,z6]),(0,[z0,z9,z4,z5,z6,z772])],[(0,[z0,z9,z4,z773,z5,z6]),(0,[z0,z9,z3,z4,z6,z774]),(0,[z12,z0,z9,z3,z174,z13])],[(0,[z0,z204,z3,z4,z5,z6]),(0,[z0,z9,z3,z610,z122,z6]),(0,[z0,z9,z3,z775,z5,z6])],[(0,[z0,z9,z3,z4,z776,z6]),(0,[z0,z3,z497,z22,z5,z6]),(0,[z250,z0,z3,z4,z124,z6]),(0,[z0,z9,z15,z5,z6,z364]),(0,[z0,z9,z3,z777,z5,z6]),(0,[z0,z9,z286,z4,z5,z31])]],
   [[(0,[z0,z336,z3,z4,z5,z42]),(0,[z0,z9,z4,z778,z5,z6]),(0,[z9,z3,z4,z5,z779,z6]),(0,[z780,z0,z9,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z34]),(0,[z0,z9,z17,z88,z5,z6]),(0,[z0,z99,z3,z4,z174,z6])],[(0,[z0,z9,z781,z4,z5,z6]),(0,[z0,z9,z782,z4,z5,z6]),(0,[z0,z9,z217,z4,z5,z18])],[(0,[z76,z1,z3,z4,z5,z56]),(0,[z0,z1,z3,z605,z5,z6]),(0,[z0,z62,z612,z4,z5,z6]),(0,[z0,z3,z505,z22,z5,z6]),(0,[z783,z1,z3,z4,z5,z6]),(0,[z0,z9,z65,z4,z510,z6])],[(0,[z0,z9,z514,z15,z5,z6]),(0,[z784,z9,z3,z4,z5,z6]),(0,[z0,z9,z4,z785,z5,z6]),(0,[z0,z3,z4,z786,z5,z6])],[(0,[z167,z1,z21,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z787]),(0,[z586,z0,z9,z3,z6,z74]),(0,[z359,z9,z3,z4,z5,z56]),(0,[z0,z420,z3,z4,z115,z6])],[(0,[z51,z722,z3,z4,z5,z6]),(0,[z0,z9,z788,z4,z5,z6]),(0,[z0,z3,z4,z789,z5,z6])],[(0,[z0,z9,z3,z4,z5,z790]),(0,[z0,z204,z3,z4,z5,z157]),(0,[z43,z9,z44,z54,z5,z6]),(0,[z9,z3,z4,z513,z35,z6]),(0,[z0,z9,z3,z791,z4,z5]),(0,[z173,z0,z3,z4,z22,z6]),(0,[z0,z4,z22,z161,z5,z6]),(0,[z318,z1,z3,z4,z5,z6]),(0,[z792,z9,z17,z4,z5,z6]),(0,[z332,z84,z3,z4,z5,z6]),(0,[z793,z9,z3,z4,z5,z6]),(0,[z0,z9,z4,z5,z794,z6])],[(0,[z51,z536,z3,z4,z5,z6]),(0,[z0,z9,z795,z4,z5,z6]),(0,[z0,z1,z245,z4,z5,z6]),(0,[z796,z9,z3,z4,z5,z6]),(0,[z711,z9,z3,z4,z5,z6]),(0,[z0,z159,z3,z4,z5,z59]),(0,[z73,z0,z9,z3,z31,z74])]],
   [[(0,[z51,z2,z4,z15,z5,z6]),(0,[z146,z722,z3,z4,z5,z6]),(0,[z0,z9,z3,z797,z5,z6]),(0,[z0,z9,z3,z4,z5,z798]),(0,[z0,z435,z4,z22,z5,z6]),(0,[z0,z1,z3,z469,z5,z6]),(0,[z799,z9,z3,z4,z5,z6]),(0,[z0,z9,z15,z5,z387,z6]),(0,[z800,z0,z17,z4,z5,z6]),(0,[z0,z84,z335,z4,z5,z6])],[(0,[z0,z801,z9,z4,z5,z6]),(0,[z7,z1,z53,z4,z5,z6]),(0,[z512,z0,z3,z22,z5,z6]),(0,[z0,z3,z4,z5,z6,z802]),(0,[z0,z9,z17,z626,z5,z6])],[(0,[z0,z9,z26,z15,z5,z6]),(0,[z0,z286,z4,z22,z5,z6]),(0,[z332,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z331,z6]),(0,[z0,z9,z3,z4,z803,z6]),(0,[z12,z0,z9,z3,z115,z13]),(0,[z0,z804,z3,z4,z5,z6])],[(0,[z287,z0,z348,z4,z5,z6]),(0,[z0,z3,z355,z22,z5,z6]),(0,[z0,z1,z3,z4,z23,z58]),(0,[z0,z9,z805,z4,z5,z6]),(0,[z0,z9,z4,z5,z6,z806]),(0,[z0,z81,z4,z161,z5,z6]),(0,[z0,z81,z162,z4,z5,z6])],[(0,[z0,z1,z3,z4,z133,z6]),(0,[z0,z9,z3,z4,z5,z807]),(0,[z0,z9,z4,z808,z5,z6]),(0,[z0,z3,z513,z22,z5,z6]),(0,[z96,z0,z105,z4,z5,z6]),(0,[z809,z9,z3,z4,z5,z6]),(0,[z0,z121,z22,z15,z5,z6]),(0,[z0,z9,z15,z5,z6,z403]),(0,[z0,z810,z3,z4,z5,z6])],[(0,[z0,z9,z3,z4,z811,z6]),(0,[z0,z9,z4,z5,z6,z812]),(0,[z20,z287,z0,z4,z5,z6]),(0,[z0,z204,z4,z15,z5,z6]),(0,[z0,z813,z3,z4,z5,z6]),(0,[z0,z9,z814,z4,z5,z6]),(0,[z113,z1,z3,z4,z5,z6]),(0,[z616,z0,z9,z4,z5,z50]),(0,[z0,z9,z3,z4,z5,z815]),(0,[z0,z99,z3,z4,z115,z6])],[(0,[z43,z225,z3,z44,z5,z6]),(0,[z43,z9,z3,z545,z5,z6]),(0,[z0,z9,z3,z816,z5,z6]),(0,[z96,z0,z60,z4,z5,z6]),(0,[z29,z0,z3,z22,z5,z6]),(0,[z250,z0,z3,z4,z5,z34]),(0,[z37,z0,z9,z4,z752,z6])],[(0,[z0,z9,z817,z4,z5,z6]),(0,[z735,z0,z9,z3,z4,z6]),(0,[z167,z9,z818,z4,z5,z6]),(0,[z8,z9,z3,z10,z5,z6]),(0,[z0,z819,z3,z4,z5,z6]),(0,[z0,z9,z4,z820,z5,z6]),(0,[z0,z9,z4,z15,z5,z34]),(0,[z250,z0,z3,z4,z5,z106]),(0,[z821,z0,z9,z4,z15,z6])]],
   [[(0,[z0,z9,z822,z4,z5,z6]),(0,[z247,z0,z3,z4,z5,z39]),(0,[z0,z9,z543,z15,z5,z6]),(0,[z9,z17,z765,z4,z5,z6]),(0,[z0,z9,z17,z506,z5,z6])],[(0,[z631,z2,z3,z4,z5,z6]),(0,[z0,z823,z3,z4,z5,z6]),(0,[z0,z9,z4,z824,z5,z6]),(0,[z0,z3,z715,z22,z5,z6])],[(0,[z0,z9,z3,z825,z5,z6]),(0,[z0,z9,z826,z4,z5,z6]),(0,[z0,z4,z193,z15,z5,z6])],[(0,[z827,z0,z3,z4,z5,z6]),(0,[z0,z828,z3,z4,z5,z6]),(0,[z829,z0,z9,z3,z5,z6]),(0,[z0,z1,z3,z4,z830,z6]),(0,[z353,z1,z3,z4,z5,z6]),(0,[z0,z831,z9,z4,z5,z6]),(0,[z0,z9,z17,z351,z5,z6]),(0,[z832,z9,z3,z4,z5,z6]),(0,[z130,z9,z335,z4,z5,z6]),(0,[z0,z9,z3,z4,z833,z6])],[(0,[z0,z9,z3,z834,z5,z6]),(0,[z0,z3,z4,z158,z5,z63]),(0,[z0,z9,z3,z4,z5,z835]),(0,[z456,z0,z4,z148,z5,z6]),(0,[z0,z836,z3,z4,z5,z6]),(0,[z12,z0,z9,z367,z5,z13]),(0,[z0,z9,z4,z837,z5,z6])],[(0,[z0,z9,z838,z4,z5,z6]),(0,[z839,z9,z3,z4,z5,z6]),(0,[z273,z0,z9,z4,z5,z6]),(0,[z0,z3,z548,z22,z5,z6]),(0,[z38,z0,z3,z4,z5,z39])],[(0,[z96,z0,z32,z4,z5,z6]),(0,[z0,z9,z3,z4,z840,z6]),(0,[z841,z9,z3,z4,z5,z6]),(0,[z0,z3,z4,z842,z5,z6]),(0,[z0,z843,z3,z4,z5,z6]),(0,[z0,z844,z3,z4,z5,z6])],[(0,[z8,z9,z3,z10,z5,z157]),(0,[z845,z0,z9,z4,z5,z6]),(0,[z250,z223,z0,z4,z5,z6])]],
   [[(0,[z55,z1,z3,z4,z35,z6]),(0,[z0,z32,z4,z554,z5,z6]),(0,[z29,z0,z164,z22,z5,z6]),(0,[z0,z9,z141,z4,z5,z18]),(0,[z0,z9,z3,z4,z6,z120])],[(0,[z7,z53,z4,z22,z5,z6]),(0,[z382,z9,z3,z4,z35,z6]),(0,[z780,z0,z1,z4,z5,z6]),(0,[z318,z9,z3,z4,z5,z25])],[(0,[z0,z9,z846,z4,z5,z6]),(0,[z0,z9,z3,z4,z847,z6]),(0,[z0,z3,z4,z5,z848,z6]),(0,[z0,z849,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z850]),(0,[z0,z9,z605,z15,z5,z6]),(0,[z273,z0,z9,z4,z5,z58]),(0,[z851,z9,z3,z4,z5,z6]),(0,[z0,z9,z4,z852,z5,z6]),(0,[z0,z162,z4,z66,z5,z6])],[(0,[z0,z9,z770,z4,z5,z6]),(0,[z0,z4,z179,z15,z5,z6]),(0,[z332,z9,z286,z4,z5,z6]),(0,[z0,z9,z3,z5,z853,z13])],[(0,[z854,z0,z3,z4,z5,z6]),(0,[z0,z9,z17,z4,z129,z6]),(0,[z9,z3,z4,z5,z6,z855]),(0,[z20,z0,z1,z4,z5,z50])],[(0,[z51,z583,z3,z4,z5,z6]),(0,[z0,z856,z3,z4,z5,z6]),(0,[z0,z857,z3,z4,z5,z6]),(0,[z0,z9,z858,z4,z5,z6]),(0,[z0,z9,z17,z4,z77,z6]),(0,[z0,z859,z3,z4,z5,z6]),(0,[z0,z3,z4,z860,z5,z6]),(0,[z0,z9,z861,z4,z5,z6]),(0,[z20,z0,z9,z4,z5,z237]),(0,[z20,z0,z9,z345,z4,z5]),(0,[z0,z9,z862,z4,z5,z6])],[(0,[z0,z1,z3,z4,z381,z6])],[(0,[z582,z9,z3,z4,z35,z6]),(0,[z73,z0,z9,z17,z6,z74]),(0,[z0,z9,z3,z863,z4,z5])]],
   [[(0,[z0,z864,z3,z4,z5,z6]),(0,[z0,z9,z4,z5,z865,z6]),(0,[z12,z0,z99,z3,z5,z13]),(0,[z0,z9,z866,z4,z5,z6])],[(0,[z0,z9,z3,z4,z867,z6]),(0,[z0,z3,z565,z22,z5,z6]),(0,[z0,z9,z571,z15,z5,z6]),(0,[z167,z9,z692,z4,z5,z6]),(0,[z0,z9,z3,z4,z868,z6]),(0,[z0,z335,z4,z22,z5,z6]),(0,[z0,z9,z869,z4,z5,z6])],[(0,[z0,z225,z3,z4,z5,z6]),(0,[z0,z9,z4,z870,z5,z6]),(0,[z0,z9,z871,z4,z5,z6]),(0,[z43,z9,z3,z525,z5,z6]),(0,[z27,z0,z3,z4,z124,z150]),(0,[z0,z872,z3,z4,z5,z6]),(0,[z0,z9,z3,z388,z5,z25])],[(0,[z0,z1,z3,z4,z396,z6]),(0,[z47,z9,z3,z4,z5,z6]),(0,[z0,z4,z22,z15,z5,z6]),(0,[z0,z9,z3,z4,z873,z6]),(0,[z0,z9,z4,z5,z6,z874]),(0,[z0,z9,z3,z4,z174,z25])],[(0,[z0,z9,z3,z4,z875,z6]),(0,[z8,z9,z3,z876,z5,z6]),(0,[z877,z9,z3,z4,z5,z6]),(0,[z38,z0,z4,z15,z5,z39]),(0,[z0,z3,z4,z5,z106,z878]),(0,[z64,z0,z9,z3,z4,z415])],[(0,[z0,z9,z3,z4,z879,z6])],[(0,[z0,z722,z3,z4,z5,z6]),(0,[z652,z0,z3,z22,z5,z6]),(0,[z0,z204,z245,z4,z5,z6]),(0,[z0,z880,z3,z4,z5,z6]),(0,[z0,z9,z881,z4,z5,z6]),(0,[z0,z17,z22,z15,z5,z6]),(0,[z0,z9,z222,z4,z15,z5])],[(0,[z0,z882,z3,z4,z5,z6]),(0,[z20,z0,z9,z4,z5,z459]),(0,[z96,z0,z881,z4,z5,z6]),(0,[z0,z164,z4,z22,z5,z6]),(0,[z9,z3,z4,z5,z6,z883]),(0,[z0,z1,z3,z4,z5,z237]),(0,[z0,z9,z4,z15,z6,z120]),(0,[z0,z420,z100,z4,z5,z6])]],
   [[(0,[z9,z3,z4,z5,z213,z6]),(0,[z0,z884,z3,z4,z5,z6]),(0,[z12,z0,z1,z3,z5,z13]),(0,[z73,z332,z9,z3,z6,z74])],[(0,[z332,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z885,z6]),(0,[z0,z1,z4,z5,z6,z886]),(0,[z0,z9,z17,z4,z254,z6]),(0,[z515,z0,z9,z3,z270,z4])],[(0,[z0,z9,z3,z4,z887,z6]),(0,[z0,z9,z367,z4,z174,z6]),(0,[z0,z9,z3,z4,z23,z58])],[(0,[z0,z9,z3,z4,z133,z6]),(0,[z0,z336,z3,z4,z5,z6]),(0,[z888,z0,z9,z4,z5,z6])],[(0,[z0,z9,z135,z4,z5,z6]),(0,[z0,z889,z3,z4,z5,z6]),(0,[z9,z3,z4,z10,z259,z6]),(0,[z0,z9,z890,z4,z5,z6]),(0,[z0,z1,z164,z4,z5,z6]),(0,[z891,z0,z9,z4,z5,z6]),(0,[z0,z9,z17,z4,z5,z186]),(0,[z47,z9,z4,z5,z93,z6]),(0,[z0,z3,z4,z892,z5,z6]),(0,[z0,z9,z4,z893,z5,z6])],[(0,[z0,z9,z3,z4,z5,z894]),(0,[z85,z9,z36,z4,z5,z16]),(0,[z0,z99,z17,z4,z5,z6]),(0,[z0,z895,z3,z4,z5,z6]),(0,[z73,z0,z151,z3,z6,z74])],[(0,[z0,z1,z3,z251,z5,z6]),(0,[z0,z9,z245,z4,z5,z157]),(0,[z0,z578,z612,z4,z5,z6]),(0,[z896,z0,z9,z4,z15,z5]),(0,[z20,z0,z9,z4,z5,z289])],[(0,[z0,z9,z3,z4,z897,z6]),(0,[z0,z4,z22,z54,z5,z6]),(0,[z0,z9,z3,z898,z5,z6]),(0,[z0,z9,z899,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z741])]],
   [[(0,[z146,z144,z3,z4,z396,z6]),(0,[z0,z3,z4,z5,z6,z152]),(0,[z302,z0,z9,z15,z5,z6]),(0,[z0,z9,z4,z137,z5,z93]),(0,[z37,z0,z9,z4,z6,z120]),(0,[z0,z99,z100,z4,z5,z6])],[(0,[z0,z225,z4,z15,z5,z6]),(0,[z0,z9,z4,z5,z900,z6]),(0,[z96,z0,z4,z148,z5,z6]),(0,[z216,z9,z3,z4,z213,z6]),(0,[z901,z9,z3,z4,z5,z6]),(0,[z0,z9,z4,z902,z5,z6]),(0,[z318,z9,z3,z4,z5,z13]),(0,[z0,z903,z3,z4,z5,z6])],[(0,[z0,z9,z904,z4,z5,z6]),(0,[z353,z9,z3,z4,z5,z6]),(0,[z0,z3,z4,z905,z5,z6]),(0,[z0,z9,z3,z4,z830,z6]),(0,[z47,z9,z4,z15,z5,z6])],[(0,[z0,z336,z3,z4,z5,z157]),(0,[z0,z9,z3,z4,z75,z34]),(0,[z27,z0,z3,z4,z124,z6]),(0,[z0,z9,z775,z15,z5,z6]),(0,[z0,z9,z17,z222,z4,z5])],[(0,[z0,z4,z45,z15,z5,z6]),(0,[z0,z22,z15,z5,z6,z13]),(0,[z0,z3,z4,z906,z5,z6]),(0,[z9,z17,z4,z5,z213,z6]),(0,[z0,z9,z4,z907,z5,z6]),(0,[z0,z159,z3,z4,z5,z878]),(0,[z0,z908,z3,z4,z5,z6]),(0,[z0,z9,z141,z4,z5,z741]),(0,[z0,z151,z335,z4,z5,z6])],[(0,[z287,z0,z17,z4,z5,z6]),(0,[z47,z3,z4,z22,z5,z6]),(0,[z0,z3,z4,z22,z873,z6]),(0,[z27,z0,z3,z4,z124,z34]),(0,[z0,z3,z4,z909,z5,z6]),(0,[z0,z9,z910,z4,z5,z6])],[(0,[z0,z348,z4,z22,z5,z6]),(0,[z0,z9,z911,z4,z5,z6]),(0,[z0,z9,z3,z4,z912,z6]),(0,[z0,z9,z3,z4,z913,z6]),(0,[z0,z9,z914,z4,z5,z6]),(0,[z0,z3,z4,z915,z5,z6]),(0,[z600,z9,z3,z10,z5,z6]),(0,[z0,z3,z22,z5,z6,z125]),(0,[z0,z4,z757,z15,z5,z6])],[(0,[z51,z253,z3,z4,z5,z6]),(0,[z8,z9,z245,z10,z5,z6]),(0,[z9,z3,z44,z876,z5,z6]),(0,[z55,z9,z3,z4,z35,z6]),(0,[z0,z9,z916,z4,z5,z6]),(0,[z0,z9,z367,z4,z115,z6])]],
   [[(0,[z43,z9,z3,z4,z259,z6]),(0,[z0,z204,z3,z4,z129,z6]),(0,[z0,z9,z917,z4,z5,z6]),(0,[z9,z3,z4,z918,z5,z6]),(0,[z0,z62,z4,z292,z5,z6]),(0,[z0,z9,z4,z15,z331,z6]),(0,[z302,z0,z196,z15,z5,z6]),(0,[z332,z9,z4,z15,z5,z6]),(0,[z0,z919,z17,z4,z5,z6]),(0,[z0,z9,z4,z5,z93,z741]),(0,[z250,z0,z3,z4,z23,z58])],[(0,[z0,z9,z183,z4,z5,z6]),(0,[z920,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z33,z34]),(0,[z94,z9,z17,z4,z5,z6]),(0,[z0,z9,z4,z15,z23,z58]),(0,[z173,z0,z9,z17,z4,z6])],[(0,[z0,z9,z4,z15,z133,z6]),(0,[z0,z9,z921,z4,z5,z6]),(0,[z146,z643,z3,z4,z5,z6]),(0,[z0,z336,z4,z15,z5,z6]),(0,[z0,z9,z3,z876,z5,z6]),(0,[z85,z1,z3,z4,z5,z16]),(0,[z0,z3,z4,z5,z878,z39])],[(0,[z9,z3,z4,z621,z35,z6]),(0,[z287,z7,z53,z4,z5,z6]),(0,[z64,z0,z9,z3,z504,z4]),(0,[z0,z9,z922,z4,z5,z6]),(0,[z130,z3,z4,z22,z5,z6]),(0,[z0,z3,z4,z22,z885,z6]),(0,[z0,z9,z3,z4,z174,z13])],[(0,[z0,z9,z923,z4,z5,z6]),(0,[z0,z9,z924,z4,z5,z6]),(0,[z456,z0,z32,z4,z5,z6]),(0,[z0,z3,z4,z22,z23,z58]),(0,[z0,z9,z4,z5,z6,z925]),(0,[z0,z17,z4,z5,z6,z152]),(0,[z37,z0,z9,z4,z49,z6]),(0,[z64,z0,z9,z3,z307,z4])],[(0,[z0,z3,z4,z22,z133,z6]),(0,[z0,z9,z3,z4,z926,z6]),(0,[z0,z9,z3,z4,z927,z6]),(0,[z0,z225,z4,z54,z5,z6]),(0,[z0,z9,z3,z4,z381,z6]),(0,[z0,z3,z4,z193,z5,z6]),(0,[z928,z9,z3,z4,z5,z6]),(0,[z0,z9,z929,z4,z5,z6]),(0,[z0,z159,z17,z4,z5,z106])],[(0,[z146,z3,z4,z374,z5,z6]),(0,[z76,z9,z3,z4,z5,z709]),(0,[z0,z3,z4,z33,z106,z58])],[(0,[z0,z9,z3,z4,z5,z930]),(0,[z0,z9,z3,z4,z5,z931]),(0,[z0,z9,z932,z4,z5,z6]),(0,[z9,z3,z876,z10,z5,z6]),(0,[z73,z130,z9,z3,z6,z74])]],
   [[(0,[z83,z144,z3,z4,z5,z6]),(0,[z43,z3,z44,z22,z5,z6]),(0,[z0,z4,z45,z54,z5,z6]),(0,[z933,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z934]),(0,[z0,z1,z100,z4,z5,z6]),(0,[z38,z0,z3,z4,z331,z39]),(0,[z0,z9,z935,z4,z5,z6])],[(0,[z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z936,z6]),(0,[z0,z9,z3,z4,z5,z709]),(0,[z353,z9,z4,z15,z5,z6])],[(0,[z0,z135,z4,z22,z5,z6]),(0,[z0,z9,z3,z4,z5,z937]),(0,[z0,z3,z4,z22,z5,z150]),(0,[z27,z0,z4,z15,z124,z6]),(0,[z0,z9,z4,z5,z752,z6]),(0,[z938,z0,z3,z4,z5,z6])],[(0,[z0,z1,z3,z311,z5,z6]),(0,[z0,z9,z939,z4,z5,z6]),(0,[z0,z9,z940,z4,z5,z6]),(0,[z0,z279,z131,z4,z5,z6])],[(0,[z353,z3,z4,z22,z5,z6]),(0,[z0,z99,z367,z4,z5,z6])],[(0,[z144,z9,z3,z4,z133,z6]),(0,[z0,z3,z4,z941,z5,z6]),(0,[z0,z9,z17,z4,z259,z6]),(0,[z0,z3,z4,z5,z942,z6]),(0,[z38,z273,z0,z4,z5,z39]),(0,[z0,z3,z91,z193,z5,z25])],[(0,[z0,z9,z943,z4,z5,z6]),(0,[z55,z9,z4,z15,z35,z6]),(0,[z27,z0,z3,z4,z326,z6]),(0,[z0,z9,z3,z4,z5,z237])],[(0,[z0,z9,z4,z944,z5,z6]),(0,[z0,z9,z3,z4,z945,z6]),(0,[z0,z9,z3,z4,z5,z946]),(0,[z19,z9,z337,z4,z5,z6]),(0,[z0,z947,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z948])]],
   [[(0,[z0,z9,z3,z4,z949,z6]),(0,[z0,z9,z3,z950,z5,z6]),(0,[z43,z9,z17,z44,z5,z6]),(0,[z20,z0,z4,z22,z5,z50]),(0,[z223,z0,z4,z22,z5,z6]),(0,[z0,z9,z4,z5,z6,z886]),(0,[z0,z196,z17,z4,z5,z6]),(0,[z0,z9,z951,z4,z5,z6])],[(0,[z0,z9,z3,z4,z5,z157]),(0,[z8,z9,z3,z10,z129,z6]),(0,[z55,z3,z4,z22,z35,z6]),(0,[z0,z952,z3,z4,z5,z6]),(0,[z0,z9,z953,z4,z5,z6]),(0,[z0,z17,z4,z193,z5,z6]),(0,[z0,z9,z141,z4,z5,z93])],[(0,[z0,z9,z14,z4,z129,z6]),(0,[z0,z9,z3,z4,z5,z954]),(0,[z0,z1,z288,z15,z5,z6]),(0,[z12,z0,z9,z100,z5,z13]),(0,[z0,z9,z3,z4,z58,z364]),(0,[z0,z9,z3,z863,z4,z6])],[(0,[z0,z1,z3,z571,z5,z6]),(0,[z85,z9,z372,z4,z5,z16]),(0,[z0,z9,z164,z4,z5,z6]),(0,[z0,z3,z664,z22,z5,z6]),(0,[z920,z3,z4,z22,z5,z6]),(0,[z0,z3,z4,z955,z5,z6])],[(0,[z0,z9,z4,z15,z381,z6]),(0,[z896,z0,z9,z3,z4,z5])],[(0,[z689,z9,z53,z4,z5,z6]),(0,[z0,z3,z222,z4,z22,z5]),(0,[z165,z0,z105,z4,z5,z6]),(0,[z956,z9,z3,z4,z5,z6])],[(0,[z0,z9,z3,z4,z957,z6]),(0,[z0,z958,z3,z4,z5,z6])],[(0,[z0,z959,z3,z4,z5,z6]),(0,[z0,z960,z3,z4,z5,z6]),(0,[z928,z3,z4,z22,z5,z6]),(0,[z0,z1,z335,z4,z5,z6]),(0,[z250,z0,z3,z4,z5,z6]),(0,[z0,z701,z3,z4,z5,z106]),(0,[z165,z0,z60,z4,z5,z6]),(0,[z20,z0,z9,z4,z5,z375]),(0,[z0,z9,z3,z863,z4,z58])]],
   [[(0,[z0,z9,z4,z15,z5,z6]),(0,[z7,z9,z818,z4,z5,z6]),(0,[z0,z961,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z129,z42]),(0,[z0,z9,z3,z4,z962,z6]),(0,[z0,z269,z4,z22,z5,z6]),(0,[z0,z9,z3,z4,z6,z963]),(0,[z0,z1,z22,z15,z5,z6]),(0,[z73,z0,z9,z15,z6,z74]),(0,[z0,z9,z3,z736,z4,z5]),(0,[z0,z9,z3,z4,z5,z31])],[(0,[z0,z151,z3,z4,z5,z186])],[(0,[z0,z9,z3,z4,z5,z964]),(0,[z0,z965,z3,z4,z5,z6]),(0,[z0,z9,z966,z4,z5,z6]),(0,[z40,z0,z9,z4,z6,z464])],[(0,[z0,z3,z4,z22,z5,z6]),(0,[z0,z336,z245,z4,z5,z6]),(0,[z0,z1,z3,z4,z174,z6]),(0,[z64,z0,z9,z3,z863,z4])],[(0,[z0,z967,z3,z4,z5,z6]),(0,[z0,z3,z22,z221,z5,z6]),(0,[z0,z1,z3,z509,z5,z6]),(0,[z0,z579,z17,z4,z5,z6]),(0,[z0,z9,z968,z4,z5,z6])],[(0,[z163,z9,z3,z4,z5,z56]),(0,[z0,z206,z4,z444,z5,z6]),(0,[z0,z3,z4,z22,z5,z34]),(0,[z0,z9,z3,z4,z620,z58]),(0,[z0,z9,z4,z15,z5,z237]),(0,[z0,z9,z3,z270,z863,z4])],[(0,[z0,z1,z348,z4,z5,z6]),(0,[z0,z9,z4,z969,z5,z6]),(0,[z0,z9,z3,z4,z970,z6]),(0,[z0,z971,z3,z4,z5,z6]),(0,[z561,z0,z9,z15,z5,z6]),(0,[z0,z9,z3,z4,z5,z878])],[(0,[z51,z2,z17,z4,z5,z6]),(0,[z750,z0,z9,z3,z4,z5]),(0,[z165,z0,z32,z4,z5,z6]),(0,[z455,z9,z4,z258,z5,z6])]],
   [[(0,[z0,z9,z972,z4,z5,z6]),(0,[z0,z973,z3,z4,z5,z6]),(0,[z0,z9,z4,z15,z5,z157]),(0,[z0,z1,z269,z4,z5,z6]),(0,[z0,z9,z4,z974,z5,z6]),(0,[z0,z141,z4,z22,z5,z93]),(0,[z0,z9,z975,z4,z5,z6]),(0,[z0,z9,z91,z15,z5,z25]),(0,[z114,z0,z9,z3,z4,z58]),(0,[z0,z9,z4,z5,z976,z6])],[(0,[z977,z0,z9,z4,z5,z6]),(0,[z9,z3,z4,z5,z978,z6]),(0,[z0,z9,z4,z198,z6,z120])],[(0,[z0,z279,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z979]),(0,[z0,z9,z980,z4,z5,z6])],[(0,[z9,z3,z4,z10,z5,z42]),(0,[z0,z3,z4,z22,z5,z157]),(0,[z0,z9,z3,z981,z5,z6]),(0,[z0,z3,z91,z22,z5,z25]),(0,[z0,z9,z3,z4,z432,z58])],[(0,[z0,z9,z4,z54,z5,z6]),(0,[z0,z204,z17,z4,z5,z6]),(0,[z0,z1,z3,z4,z129,z6]),(0,[z0,z9,z982,z4,z5,z6]),(0,[z0,z81,z3,z4,z5,z6]),(0,[z983,z9,z3,z4,z5,z6]),(0,[z20,z0,z9,z3,z4,z120])],[(0,[z0,z1,z3,z4,z77,z6]),(0,[z0,z91,z22,z15,z5,z6]),(0,[z0,z9,z4,z984,z5,z6]),(0,[z0,z9,z17,z91,z5,z25]),(0,[z47,z9,z3,z4,z6,z58]),(0,[z0,z9,z3,z863,z4,z23])],[(0,[z0,z3,z4,z985,z5,z6]),(0,[z0,z3,z4,z986,z5,z6]),(0,[z393,z0,z3,z22,z5,z6]),(0,[z1,z3,z4,z5,z779,z6]),(0,[z250,z0,z4,z15,z5,z6])],[(0,[z0,z17,z4,z22,z5,z6]),(0,[z0,z9,z4,z15,z5,z31]),(0,[z0,z9,z100,z4,z5,z6]),(0,[z0,z987,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z6,z712])]],
   [[(0,[z0,z3,z4,z988,z5,z6]),(0,[z989,z0,z9,z3,z4,z6]),(0,[z76,z9,z3,z4,z381,z56]),(0,[z990,z9,z3,z4,z5,z6]),(0,[z0,z62,z241,z4,z5,z6]),(0,[z0,z9,z991,z4,z5,z6]),(0,[z0,z1,z3,z4,z115,z6]),(0,[z0,z9,z992,z4,z5,z6])],[(0,[z0,z204,z3,z4,z259,z6]),(0,[z0,z9,z3,z4,z5,z993])],[(0,[z0,z9,z3,z4,z994,z6]),(0,[z287,z0,z206,z4,z5,z6]),(0,[z0,z245,z4,z22,z5,z6]),(0,[z434,z9,z3,z4,z35,z6]),(0,[z0,z9,z995,z4,z5,z6]),(0,[z0,z3,z4,z22,z5,z31]),(0,[z996,z0,z4,z22,z5,z6]),(0,[z997,z9,z3,z4,z5,z6])],[(0,[z43,z9,z269,z44,z5,z6]),(0,[z0,z9,z3,z4,z998,z6]),(0,[z0,z431,z3,z4,z5,z59]),(0,[z0,z3,z4,z999,z5,z6]),(0,[z20,z37,z0,z9,z4,z58]),(0,[z353,z9,z3,z4,z174,z6])],[(0,[z0,z194,z3,z4,z5,z6]),(0,[z76,z9,z3,z4,z5,z56]),(0,[z1000,z9,z3,z4,z5,z6]),(0,[z83,z126,z3,z4,z5,z6]),(0,[z783,z9,z3,z4,z5,z6]),(0,[z0,z578,z4,z292,z5,z6]),(0,[z0,z9,z3,z4,z6,z1001])],[(0,[z0,z9,z4,z1002,z5,z6]),(0,[z0,z9,z17,z554,z5,z6]),(0,[z0,z1,z4,z333,z5,z6]),(0,[z796,z9,z17,z4,z5,z6]),(0,[z711,z9,z17,z4,z5,z6]),(0,[z0,z151,z17,z4,z5,z6]),(0,[z792,z9,z3,z4,z5,z6])],[(0,[z1003,z0,z9,z4,z5,z6]),(0,[z167,z9,z21,z4,z5,z6]),(0,[z0,z9,z1004,z4,z5,z6]),(0,[z0,z3,z4,z1005,z5,z6]),(0,[z9,z3,z4,z5,z16,z709]),(0,[z0,z940,z4,z22,z5,z6]),(0,[z139,z9,z4,z366,z5,z6]),(0,[z87,z0,z9,z4,z599,z6])],[(0,[z0,z9,z3,z4,z1006,z6]),(0,[z43,z9,z3,z4,z5,z42]),(0,[z0,z420,z17,z4,z5,z6]),(0,[z800,z0,z3,z4,z5,z6]),(0,[z37,z113,z9,z4,z49,z6])]],
   [[(0,[z318,z9,z3,z4,z5,z6]),(0,[z440,z9,z3,z4,z5,z16]),(0,[z0,z62,z206,z4,z5,z6]),(0,[z0,z9,z15,z5,z6,z473]),(0,[z0,z84,z3,z4,z5,z186]),(0,[z0,z9,z1007,z4,z5,z6]),(0,[z0,z9,z3,z4,z276,z58]),(0,[z12,z318,z9,z3,z5,z13])],[(0,[z0,z9,z245,z4,z5,z6]),(0,[z1008,z9,z3,z4,z5,z6]),(0,[z0,z1,z17,z22,z5,z6]),(0,[z0,z1,z3,z4,z254,z6]),(0,[z273,z0,z9,z270,z4,z5]),(0,[z0,z279,z4,z15,z5,z6]),(0,[z173,z0,z9,z4,z15,z6])],[(0,[z55,z9,z3,z4,z1009,z6]),(0,[z96,z0,z316,z4,z5,z6]),(0,[z9,z3,z4,z5,z1010,z6]),(0,[z0,z9,z4,z5,z1011,z6]),(1,[z0,z9,z3,z863,z4])],[(0,[z52,z9,z348,z4,z5,z6]),(0,[z7,z9,z53,z4,z5,z6]),(0,[z0,z1012,z3,z4,z5,z6]),(0,[z12,z0,z3,z22,z5,z13]),(0,[z0,z9,z3,z4,z5,z1013]),(0,[z1014,z9,z3,z4,z5,z6]),(0,[z0,z81,z4,z15,z5,z6]),(0,[z0,z9,z17,z4,z5,z815]),(0,[z73,z0,z9,z286,z6,z74])],[(0,[z0,z9,z3,z4,z5,z1015]),(0,[z0,z1016,z3,z4,z5,z6]),(0,[z43,z3,z44,z45,z5,z6]),(0,[z0,z3,z4,z1017,z5,z6]),(0,[z0,z9,z4,z1018,z5,z6]),(0,[z600,z0,z9,z3,z5,z13]),(0,[z29,z0,z17,z22,z5,z6]),(0,[z0,z3,z4,z22,z5,z979]),(0,[z0,z1,z3,z4,z5,z186]),(0,[z27,z0,z3,z4,z887,z6]),(0,[z0,z9,z3,z4,z331,z6]),(0,[z0,z1019,z3,z4,z5,z6]),(0,[z0,z9,z4,z268,z218,z6])],[(0,[z0,z9,z519,z15,z5,z6]),(0,[z8,z9,z17,z10,z5,z6]),(0,[z0,z9,z3,z4,z1020,z6]),(0,[z0,z1021,z3,z4,z5,z6]),(0,[z0,z334,z3,z4,z5,z6]),(0,[z0,z3,z4,z22,z6,z120]),(0,[z0,z1,z65,z4,z218,z6]),(0,[z0,z9,z479,z15,z5,z6]),(0,[z64,z47,z9,z3,z4,z6]),(0,[z73,z0,z9,z3,z6,z74])],[(0,[z0,z9,z1022,z4,z5,z6]),(0,[z0,z9,z3,z4,z35,z34]),(0,[z0,z1,z4,z5,z6,z177]),(0,[z0,z9,z335,z4,z5,z6]),(0,[z9,z3,z4,z5,z6,z1023])],[(0,[z113,z9,z3,z4,z5,z6]),(0,[z0,z9,z4,z1024,z5,z6]),(0,[z37,z0,z9,z636,z4,z6]),(0,[z0,z9,z1025,z4,z5,z6])]],
   [[(0,[z51,z2,z348,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z1026]),(0,[z0,z9,z1027,z4,z5,z6]),(1,[z0,z881,z4,z5,z6]),(0,[z821,z0,z9,z3,z4,z6]),(0,[z1028,z9,z3,z4,z5,z6]),(0,[z1029,z9,z3,z4,z5,z6]),(0,[z353,z9,z3,z4,z115,z6]),(0,[z1030,z0,z9,z4,z5,z6])],[(0,[z0,z1031,z9,z4,z5,z6]),(0,[z273,z0,z1,z4,z5,z6]),(0,[z40,z0,z9,z4,z49,z6]),(0,[z0,z9,z1032,z4,z5,z6])],[(0,[z0,z9,z1033,z4,z5,z6]),(0,[z8,z9,z3,z10,z259,z6]),(0,[z0,z9,z1034,z4,z5,z6]),(0,[z154,z9,z3,z4,z35,z6]),(0,[z0,z9,z3,z4,z1035,z6]),(0,[z0,z9,z3,z4,z174,z6]),(0,[z0,z1036,z3,z4,z5,z6])],[(0,[z0,z1037,z3,z4,z5,z6]),(0,[z0,z194,z4,z15,z5,z6]),(0,[z0,z9,z14,z4,z259,z6]),(0,[z76,z9,z4,z15,z5,z56]),(0,[z0,z1,z3,z4,z5,z1038]),(0,[z0,z1,z3,z222,z4,z5]),(0,[z38,z0,z17,z4,z5,z39]),(0,[z1000,z9,z4,z15,z5,z6]),(0,[z0,z9,z4,z15,z6,z1001]),(0,[z130,z9,z3,z4,z5,z186]),(0,[z0,z151,z286,z4,z5,z6])],[(0,[z0,z9,z17,z4,z5,z42]),(0,[z0,z3,z4,z1039,z5,z6]),(0,[z29,z0,z435,z22,z5,z6]),(0,[z302,z0,z22,z15,z5,z6]),(0,[z0,z1040,z3,z4,z5,z6])],[(0,[z144,z3,z4,z5,z503,z6]),(0,[z52,z287,z3,z4,z5,z6]),(0,[z0,z3,z22,z5,z6,z491]),(0,[z1041,z9,z17,z4,z5,z6])],[(0,[z76,z3,z4,z22,z5,z56]),(0,[z1000,z3,z4,z22,z5,z6]),(0,[z0,z9,z1042,z4,z5,z6]),(0,[z0,z9,z121,z15,z122,z6]),(0,[z1043,z9,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z1044])],[(0,[z0,z206,z343,z4,z5,z6]),(0,[z0,z9,z269,z4,z5,z6]),(0,[z27,z0,z3,z4,z192,z6]),(0,[z318,z9,z4,z15,z5,z6]),(0,[z12,z0,z420,z3,z5,z13])]],
   [[],[(0,[z0,z206,z348,z4,z5,z6]),(0,[z0,z9,z1045,z4,z5,z6]),(0,[z0,z1,z3,z463,z5,z6]),(0,[z0,z477,z206,z4,z5,z6]),(0,[z0,z9,z3,z4,z259,z42]),(0,[z3,z4,z22,z5,z6,z883]),(0,[z94,z1,z3,z4,z5,z6]),(0,[z0,z9,z17,z457,z5,z6])],[(0,[z0,z9,z1046,z4,z5,z6]),(0,[z318,z3,z4,z22,z5,z6]),(0,[z3,z4,z22,z5,z213,z6]),(0,[z250,z0,z3,z4,z331,z6]),(0,[z0,z9,z4,z713,z15,z5]),(0,[z0,z1047,z3,z4,z5,z6]),(0,[z64,z0,z9,z3,z270,z4])],[(0,[z0,z1048,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z129,z6]),(0,[z0,z9,z3,z4,z1049,z6]),(0,[z0,z881,z32,z4,z5,z6]),(0,[z0,z9,z3,z4,z1050,z6]),(0,[z0,z9,z3,z4,z524,z58]),(0,[z332,z9,z3,z4,z5,z31]),(0,[z0,z9,z3,z4,z31,z74])],[(0,[z0,z269,z4,z45,z5,z6]),(0,[z0,z334,z4,z15,z5,z6]),(0,[z0,z84,z17,z4,z5,z6]),(0,[z0,z9,z3,z4,z1051,z6])],[(0,[z0,z9,z3,z4,z5,z1052]),(0,[z455,z9,z53,z4,z5,z6]),(0,[z341,z9,z21,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z1053]),(0,[z223,z0,z9,z4,z5,z6]),(0,[z0,z9,z335,z4,z5,z31]),(0,[z0,z9,z286,z4,z5,z186]),(0,[z12,z0,z9,z3,z5,z853])],[(0,[z0,z9,z3,z4,z5,z1054]),(0,[z332,z3,z4,z22,z5,z6]),(0,[z0,z3,z4,z22,z331,z6]),(0,[z113,z9,z4,z15,z5,z6]),(0,[z12,z0,z9,z17,z5,z13]),(0,[z0,z9,z3,z4,z552,z58]),(0,[z0,z420,z367,z4,z5,z6])],[(0,[z0,z3,z4,z45,z5,z6]),(0,[z0,z9,z3,z4,z1055,z6]),(0,[z85,z9,z3,z4,z5,z709]),(0,[z0,z62,z881,z4,z5,z6]),(0,[z0,z9,z3,z4,z6,z1056]),(0,[z0,z9,z3,z715,z5,z6]),(0,[z0,z9,z4,z5,z6,z1057]),(0,[z38,z0,z3,z4,z5,z34]),(0,[z1058,z0,z9,z4,z15,z6]),(0,[z0,z1059,z3,z4,z5,z6]),(0,[z37,z0,z9,z4,z198,z6]),(0,[z0,z9,z3,z4,z115,z6])]],
   [[(0,[z0,z9,z4,z5,z6,z1060]),(0,[z0,z1,z17,z4,z5,z6]),(0,[z0,z9,z1061,z4,z5,z6])],[(0,[z0,z9,z155,z15,z5,z6]),(0,[z0,z9,z3,z4,z5,z1062]),(0,[z0,z9,z1063,z4,z5,z6]),(0,[z9,z3,z4,z357,z5,z56]),(0,[z113,z3,z4,z22,z5,z6]),(0,[z0,z9,z4,z15,z174,z6]),(0,[z47,z9,z17,z4,z5,z6]),(0,[z0,z9,z3,z4,z360,z58])],[(0,[z250,z0,z3,z4,z75,z6]),(0,[z0,z9,z4,z1064,z5,z6])],[(0,[z144,z722,z3,z4,z5,z6]),(0,[z1065,z0,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z129,z157]),(0,[z0,z9,z4,z1066,z5,z6])],[(0,[z0,z1067,z3,z4,z5,z6]),(0,[z0,z9,z4,z333,z5,z6]),(0,[z0,z3,z4,z22,z174,z6]),(0,[z20,z47,z9,z4,z5,z6]),(0,[z0,z9,z4,z5,z6,z1068])],[(0,[z0,z9,z3,z4,z396,z6]),(0,[z410,z0,z9,z15,z5,z6]),(0,[z0,z1069,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z1070]),(0,[z0,z1,z3,z4,z259,z6])],[(0,[z649,z9,z3,z4,z35,z6]),(0,[z215,z583,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z213,z6]),(0,[z0,z9,z4,z268,z90,z6]),(0,[z37,z0,z9,z3,z4,z237]),(0,[z0,z9,z1071,z4,z5,z6]),(0,[z318,z9,z100,z4,z5,z6])],[(0,[z0,z9,z4,z1072,z5,z6]),(0,[z0,z782,z4,z22,z5,z6]),(0,[z616,z0,z9,z4,z5,z112]),(0,[z130,z9,z17,z4,z5,z6]),(0,[z173,z0,z9,z3,z4,z6]),(0,[z0,z3,z1073,z4,z5,z6])]],
   [[(0,[z0,z9,z1074,z4,z5,z6]),(0,[z9,z3,z4,z5,z709,z56]),(0,[z0,z1,z435,z4,z5,z6]),(0,[z0,z9,z1075,z4,z5,z6]),(0,[z0,z9,z3,z4,z254,z6]),(0,[z250,z0,z3,z4,z33,z6]),(0,[z0,z1076,z3,z4,z5,z6]),(0,[z231,z0,z9,z4,z5,z289]),(0,[z0,z9,z17,z4,z23,z58])],[(0,[z0,z9,z17,z4,z133,z6]),(0,[z0,z3,z457,z22,z5,z6]),(0,[z0,z1,z3,z4,z1077,z6])],[(0,[z0,z9,z1078,z4,z5,z6]),(0,[z9,z818,z53,z4,z5,z6]),(0,[z0,z9,z4,z15,z129,z6]),(0,[z3,z4,z22,z918,z5,z6]),(0,[z0,z84,z286,z4,z5,z6]),(0,[z73,z0,z9,z335,z6,z74])],[(0,[z427,z9,z3,z4,z5,z56]),(0,[z43,z9,z3,z876,z5,z6]),(0,[z0,z17,z4,z45,z5,z6]),(0,[z0,z1,z17,z15,z5,z6]),(0,[z0,z9,z4,z5,z741,z50]),(0,[z0,z9,z3,z4,z5,z186])],[(0,[z0,z1079,z3,z4,z5,z6]),(0,[z302,z0,z1,z15,z5,z6]),(0,[z0,z9,z17,z639,z5,z6]),(0,[z0,z3,z4,z23,z152,z58])],[(0,[z146,z144,z17,z4,z5,z6]),(0,[z0,z3,z4,z1080,z5,z6]),(0,[z0,z9,z4,z5,z6,z177]),(0,[z0,z3,z4,z33,z331,z6])],[(0,[z0,z9,z1081,z4,z5,z6]),(0,[z7,z194,z53,z4,z5,z6]),(0,[z0,z1,z372,z4,z5,z6]),(0,[z0,z9,z1082,z4,z5,z6]),(0,[z0,z3,z881,z4,z5,z6]),(0,[z0,z1,z286,z4,z5,z6]),(0,[z0,z9,z4,z1083,z5,z6]),(0,[z0,z9,z17,z4,z5,z150]),(0,[z0,z9,z4,z15,z115,z6])],[(0,[z0,z9,z3,z4,z1084,z6]),(0,[z0,z9,z3,z4,z6,z1085]),(0,[z0,z1086,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z1087])]],
   [[(0,[z0,z9,z1088,z4,z5,z6]),(0,[z0,z204,z3,z4,z5,z42]),(0,[z0,z1,z3,z4,z737,z6]),(0,[z1089,z9,z3,z4,z5,z6])],[(0,[z0,z3,z4,z22,z115,z6]),(0,[z0,z3,z4,z1090,z5,z6]),(0,[z0,z9,z141,z4,z5,z198])],[(0,[z0,z3,z4,z22,z381,z6]),(0,[z0,z9,z3,z4,z5,z1038]),(0,[z0,z9,z3,z222,z4,z5]),(0,[z0,z9,z4,z5,z93,z237]),(1,[z0,z9,z3,z5,z853])],[(0,[z0,z9,z1091,z4,z5,z6]),(0,[z0,z9,z4,z1092,z5,z6]),(0,[z0,z9,z4,z1093,z5,z6]),(0,[z0,z22,z15,z5,z6,z74]),(0,[z1094,z9,z3,z4,z5,z6]),(0,[z1095,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z647,z58]),(0,[z353,z9,z100,z4,z5,z6])],[(0,[z287,z0,z3,z4,z5,z6]),(0,[z0,z9,z1096,z4,z5,z6]),(0,[z0,z9,z4,z15,z396,z6]),(0,[z85,z9,z3,z4,z5,z262]),(0,[z9,z3,z4,z1009,z35,z6]),(0,[z0,z1097,z3,z4,z5,z6]),(0,[z0,z578,z206,z4,z5,z6]),(0,[z0,z9,z1098,z4,z5,z6]),(0,[z0,z1,z4,z5,z198,z6]),(0,[z0,z9,z15,z5,z6,z706]),(0,[z0,z4,z193,z570,z5,z6]),(0,[z1099,z9,z3,z4,z5,z6])],[(0,[z0,z9,z3,z4,z5,z1100]),(0,[z0,z9,z3,z4,z1101,z6]),(0,[z0,z4,z22,z5,z6,z1057]),(0,[z130,z9,z286,z4,z5,z6]),(0,[z1102,z9,z3,z4,z5,z6])],[(0,[z0,z9,z1103,z4,z5,z6]),(0,[z29,z0,z22,z15,z5,z6]),(0,[z1104,z0,z9,z4,z5,z34]),(0,[z0,z9,z4,z1105,z5,z6])],[(0,[z0,z9,z3,z4,z1106,z6]),(0,[z0,z9,z3,z4,z5,z1107]),(0,[z0,z3,z4,z22,z396,z6]),(0,[z1108,z9,z3,z4,z5,z6]),(0,[z996,z0,z9,z4,z5,z6]),(0,[z0,z1,z367,z4,z5,z6]),(0,[z0,z9,z1109,z4,z5,z6]),(0,[z0,z9,z4,z15,z254,z6])]],
   [[(0,[z94,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z1110,z6]),(1,[z9,z818,z4,z5,z6]),(0,[z37,z0,z1,z4,z49,z6]),(0,[z0,z9,z4,z5,z1111,z34]),(0,[z0,z1112,z3,z4,z5,z6]),(0,[z0,z1113,z3,z4,z5,z6]),(0,[z1114,z0,z3,z4,z5,z6]),(0,[z0,z3,z4,z1115,z5,z6])],[(0,[z37,z0,z9,z4,z416,z6]),(0,[z332,z9,z335,z4,z5,z6]),(0,[z318,z9,z3,z4,z174,z6])],[(0,[z8,z9,z10,z15,z5,z6]),(0,[z0,z4,z22,z333,z5,z6]),(0,[z0,z9,z4,z15,z5,z186])],[(0,[z0,z9,z3,z4,z1116,z6]),(0,[z0,z9,z463,z15,z5,z6]),(0,[z0,z1117,z3,z4,z5,z6]),(0,[z8,z9,z14,z10,z5,z6]),(0,[z0,z225,z269,z4,z5,z6]),(0,[z0,z9,z1118,z4,z5,z6]),(0,[z0,z3,z4,z22,z5,z237]),(0,[z0,z9,z4,z1119,z5,z6]),(1,[z0,z9,z4,z5,z741])],[(0,[z0,z3,z261,z22,z5,z6]),(0,[z85,z9,z3,z4,z5,z16]),(0,[z631,z3,z4,z190,z5,z6])],[(0,[z0,z9,z3,z4,z1120,z6]),(0,[z0,z1,z3,z91,z5,z25]),(0,[z1058,z0,z9,z3,z4,z6])],[(0,[z9,z818,z3,z4,z5,z6]),(0,[z0,z9,z3,z1121,z4,z5]),(0,[z0,z9,z17,z4,z6,z774])],[(0,[z0,z9,z17,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z1122]),(0,[z0,z9,z3,z1123,z4,z5]),(0,[z0,z9,z3,z4,z1124,z6]),(0,[z38,z0,z3,z4,z254,z39]),(0,[z1089,z9,z4,z15,z5,z6]),(0,[z0,z131,z4,z193,z5,z6])]],
   [[(0,[z0,z62,z4,z221,z5,z6]),(0,[z1125,z0,z3,z4,z5,z6]),(0,[z1126,z9,z3,z4,z5,z6]),(0,[z0,z9,z1127,z4,z5,z6]),(0,[z719,z0,z9,z17,z4,z6]),(0,[z0,z9,z4,z5,z6,z1128])],[(0,[z7,z9,z337,z4,z5,z6]),(0,[z8,z9,z3,z10,z5,z42]),(0,[z0,z3,z4,z179,z5,z6]),(0,[z1129,z0,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z1130]),(0,[z0,z9,z17,z4,z5,z34]),(0,[z0,z1131,z3,z4,z5,z6])],[(0,[z0,z9,z14,z4,z5,z42]),(0,[z12,z353,z9,z3,z5,z13])],[(0,[z287,z0,z4,z15,z5,z6]),(0,[z0,z9,z245,z4,z129,z6]),(0,[z8,z0,z22,z15,z5,z6]),(0,[z0,z4,z22,z5,z6,z177]),(0,[z1132,z9,z3,z4,z5,z6])],[(0,[z0,z9,z3,z4,z259,z6]),(0,[z0,z9,z1133,z4,z5,z6])],[(0,[z0,z9,z1134,z4,z5,z6]),(0,[z0,z9,z460,z15,z5,z6]),(0,[z20,z0,z9,z4,z5,z577]),(0,[z0,z9,z4,z1135,z5,z6]),(0,[z796,z1,z3,z4,z5,z6]),(1,[z0,z9,z4,z752,z6]),(0,[z0,z9,z141,z4,z93,z120]),(0,[z0,z9,z131,z91,z5,z25])],[(0,[z29,z0,z3,z715,z5,z6]),(0,[z0,z1136,z3,z4,z5,z6]),(0,[z1137,z9,z3,z4,z5,z6]),(0,[z318,z9,z3,z4,z115,z6])],[(0,[z0,z9,z17,z4,z5,z157]),(0,[z0,z9,z3,z4,z5,z1138]),(0,[z0,z9,z435,z4,z5,z6]),(0,[z0,z196,z3,z4,z5,z6]),(0,[z0,z1,z3,z121,z122,z6]),(0,[z94,z9,z4,z15,z5,z6])]],
   [[(0,[z0,z336,z3,z4,z129,z6]),(0,[z0,z9,z3,z4,z584,z58]),(0,[z0,z162,z4,z22,z5,z6]),(0,[z0,z9,z3,z4,z1077,z6]),(0,[z9,z3,z4,z213,z6,z58]),(0,[z1139,z9,z3,z4,z5,z6]),(0,[z413,z0,z9,z3,z270,z4]),(0,[z166,z0,z9,z15,z5,z6]),(0,[z0,z4,z5,z198,z6,z152])],[(0,[z0,z9,z1140,z4,z5,z6]),(0,[z0,z9,z4,z218,z752,z6]),(0,[z223,z0,z9,z4,z23,z58])],[(0,[z0,z9,z3,z4,z1141,z5])],[(0,[z287,z0,z32,z4,z5,z6]),(0,[z0,z3,z4,z1142,z5,z6]),(0,[z85,z9,z4,z15,z5,z16]),(0,[z0,z3,z4,z5,z6,z1143]),(0,[z64,z9,z3,z4,z213,z6]),(0,[z37,z0,z9,z4,z599,z6]),(0,[z73,z0,z84,z3,z6,z74]),(0,[z73,z0,z9,z3,z186,z74]),(0,[z1144,z0,z9,z4,z5,z6])],[(0,[z0,z9,z3,z4,z1145,z6]),(0,[z0,z9,z3,z4,z259,z157]),(0,[z0,z3,z4,z1146,z5,z6]),(0,[z821,z0,z3,z4,z22,z6]),(0,[z130,z151,z3,z4,z5,z6]),(0,[z1147,z9,z3,z4,z5,z6]),(0,[z0,z1148,z3,z4,z5,z6])],[(0,[z0,z1149,z3,z4,z5,z6]),(0,[z8,z1,z3,z10,z5,z6]),(0,[z250,z0,z17,z4,z5,z6]),(0,[z0,z17,z4,z179,z5,z6]),(0,[z0,z9,z1150,z4,z5,z6])],[(0,[z0,z1,z14,z4,z5,z6]),(0,[z85,z3,z4,z22,z5,z16]),(0,[z0,z1,z3,z4,z5,z1151]),(0,[z27,z0,z3,z4,z331,z6]),(0,[z0,z9,z17,z4,z5,z31]),(0,[z0,z1152,z3,z4,z5,z6])],[(0,[z0,z9,z3,z4,z1153,z6]),(0,[z0,z3,z4,z1154,z5,z6]),(0,[z0,z9,z1155,z4,z5,z6]),(0,[z0,z9,z1156,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z1157]),(0,[z12,z0,z9,z15,z5,z13])]],
   [[(0,[z0,z9,z3,z4,z124,z34]),(0,[z0,z3,z4,z33,z6,z454]),(0,[z0,z9,z4,z137,z5,z285]),(0,[z0,z1158,z3,z4,z5,z6])],[(0,[z0,z9,z3,z1159,z5,z6]),(0,[z0,z9,z3,z4,z5,z1160]),(0,[z0,z9,z1161,z4,z5,z6]),(0,[z0,z9,z1162,z4,z5,z6]),(0,[z0,z9,z24,z4,z510,z6]),(0,[z1163,z9,z3,z4,z5,z6]),(0,[z558,z0,z9,z3,z6,z74])],[(0,[z0,z9,z3,z4,z5,z1164]),(0,[z0,z9,z4,z1165,z5,z6]),(0,[z0,z9,z3,z4,z1166,z6]),(0,[z0,z9,z65,z4,z752,z6])],[(0,[z0,z9,z4,z15,z259,z6]),(0,[z0,z1167,z3,z4,z5,z6]),(0,[z0,z1,z36,z4,z5,z6]),(0,[z0,z579,z3,z4,z5,z6]),(0,[z0,z172,z206,z4,z5,z6]),(0,[z0,z3,z4,z22,z5,z1130]),(0,[z0,z1,z4,z570,z5,z6]),(0,[z0,z9,z4,z5,z198,z6])],[(0,[z0,z1,z3,z4,z5,z42]),(0,[z586,z9,z3,z10,z5,z6]),(0,[z1168,z0,z9,z3,z4,z6]),(0,[z0,z9,z3,z4,z111,z58]),(0,[z832,z9,z17,z4,z5,z6]),(0,[z0,z1169,z3,z4,z5,z6])],[(0,[z0,z1170,z3,z4,z5,z6]),(0,[z1171,z0,z3,z4,z5,z6]),(0,[z0,z1172,z3,z4,z5,z6]),(0,[z0,z9,z1173,z4,z5,z6]),(0,[z0,z3,z4,z1174,z5,z6])],[(0,[z9,z4,z15,z5,z213,z6]),(0,[z0,z196,z4,z15,z5,z6]),(0,[z0,z9,z367,z4,z5,z6]),(0,[z0,z9,z3,z1175,z4,z5]),(0,[z0,z9,z3,z4,z1176,z6]),(0,[z332,z9,z3,z4,z5,z186])],[(0,[z0,z304,z3,z22,z5,z6]),(0,[z0,z9,z316,z15,z5,z6]),(0,[z0,z3,z4,z22,z994,z6])]],
   [[(0,[z0,z9,z348,z4,z5,z6]),(0,[z0,z9,z324,z15,z5,z6]),(0,[z64,z0,z9,z270,z4,z15]),(0,[z0,z279,z17,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z1177])],[(0,[z96,z0,z348,z4,z5,z6]),(0,[z0,z9,z4,z15,z1141,z5]),(0,[z0,z9,z17,z4,z6,z120])],[(0,[z1178,z0,z9,z4,z5,z6]),(0,[z0,z3,z316,z22,z5,z6]),(0,[z0,z367,z4,z22,z5,z6]),(0,[z27,z9,z3,z4,z213,z6]),(0,[z0,z81,z17,z4,z5,z6])],[(0,[z167,z9,z4,z366,z5,z6]),(0,[z0,z9,z3,z5,z6,z1179]),(0,[z0,z9,z3,z4,z1180,z6]),(0,[z0,z9,z3,z4,z5,z1181]),(0,[z0,z9,z3,z4,z5,z853])],[(0,[z0,z3,z4,z22,z1141,z5]),(0,[z3,z4,z22,z5,z1010,z6]),(0,[z1182,z9,z3,z4,z5,z6]),(0,[z0,z9,z1183,z4,z5,z6]),(0,[z0,z9,z3,z91,z5,z25])],[(0,[z236,z9,z53,z4,z5,z6]),(0,[z250,z0,z3,z4,z35,z6])],[(0,[z0,z9,z1184,z4,z5,z6]),(0,[z0,z9,z4,z1185,z5,z6]),(0,[z0,z9,z3,z1186,z5,z6]),(0,[z0,z9,z4,z1187,z5,z6]),(0,[z0,z3,z22,z5,z654,z6]),(0,[z0,z9,z1188,z4,z5,z6]),(0,[z0,z4,z15,z5,z6,z152]),(0,[z0,z9,z3,z5,z6,z853])],[(0,[z722,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z77,z6]),(0,[z330,z0,z3,z4,z6,z168]),(0,[z0,z9,z4,z775,z5,z6])]],
   [[(0,[z0,z9,z17,z92,z5,z6]),(1,[z9,z3,z876,z5,z6]),(0,[z0,z1,z3,z4,z1189,z6]),(0,[z1190,z9,z3,z4,z5,z6]),(0,[z78,z0,z9,z15,z5,z6]),(0,[z20,z0,z9,z4,z5,z50]),(0,[z0,z9,z1191,z4,z5,z6]),(0,[z353,z99,z3,z4,z5,z6])],[(0,[z9,z348,z4,z5,z35,z6]),(0,[z0,z9,z3,z4,z5,z1192]),(0,[z9,z3,z4,z5,z1193,z6]),(0,[z47,z1,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z331,z39]),(0,[z0,z1194,z3,z4,z5,z6]),(0,[z250,z0,z4,z5,z198,z6])],[(0,[z0,z194,z17,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z1195]),(0,[z0,z9,z1196,z4,z5,z6]),(0,[z76,z9,z17,z4,z5,z56]),(0,[z0,z579,z4,z15,z5,z6])],[(0,[z0,z9,z1197,z4,z5,z6]),(0,[z0,z225,z17,z4,z5,z6]),(0,[z0,z9,z1198,z4,z5,z6]),(0,[z0,z3,z639,z22,z5,z6]),(0,[z0,z100,z4,z22,z5,z6]),(0,[z0,z3,z22,z5,z6,z662]),(0,[z20,z0,z9,z4,z5,z741]),(0,[z130,z84,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z1199]),(0,[z0,z3,z4,z1200,z5,z6])],[(0,[z0,z9,z4,z1201,z5,z6]),(0,[z0,z151,z3,z4,z5,z6]),(0,[z37,z0,z4,z22,z49,z6]),(0,[z0,z3,z4,z22,z1166,z6]),(0,[z0,z1,z3,z479,z5,z6]),(0,[z1171,z0,z4,z15,z5,z6]),(0,[z0,z9,z4,z1202,z15,z6])],[(0,[z0,z9,z1203,z4,z5,z6]),(0,[z0,z3,z4,z66,z5,z6]),(0,[z0,z3,z4,z5,z6,z878]),(0,[z0,z9,z3,z4,z1204,z6]),(0,[z0,z9,z3,z4,z5,z1205]),(0,[z0,z9,z3,z4,z1206,z6]),(0,[z1207,z9,z3,z4,z5,z6])],[(0,[z0,z9,z3,z4,z1208,z6]),(0,[z0,z420,z3,z4,z5,z6]),(0,[z330,z0,z3,z4,z124,z6]),(0,[z0,z1,z3,z480,z5,z6]),(0,[z9,z4,z15,z918,z5,z6]),(0,[z318,z9,z17,z4,z5,z6])],[(0,[z51,z9,z3,z4,z133,z6]),(0,[z0,z9,z1209,z4,z5,z6]),(0,[z30,z9,z21,z4,z5,z6]),(0,[z43,z0,z22,z15,z5,z6]),(1,[z9,z3,z4,z5,z709]),(0,[z130,z1,z3,z4,z5,z6]),(0,[z9,z3,z4,z5,z1210,z6]),(0,[z0,z1211,z3,z4,z5,z6]),(0,[z1212,z9,z3,z4,z5,z6])]],
   [[(0,[z167,z21,z4,z22,z5,z6]),(0,[z0,z1213,z3,z4,z5,z6]),(0,[z0,z1,z3,z22,z5,z6]),(0,[z0,z1,z131,z4,z5,z6]),(0,[z0,z9,z1214,z4,z5,z6]),(0,[z0,z3,z4,z1215,z5,z6]),(0,[z0,z3,z4,z1216,z5,z6]),(0,[z0,z4,z66,z161,z5,z6]),(0,[z0,z9,z3,z91,z5,z853])],[(0,[z73,z0,z3,z22,z6,z74]),(0,[z0,z4,z22,z5,z198,z6]),(0,[z73,z0,z1,z3,z6,z74]),(0,[z130,z9,z3,z4,z6,z74])],[(0,[z0,z1,z135,z4,z5,z6]),(0,[z145,z9,z53,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z1217]),(0,[z0,z1218,z3,z4,z5,z6]),(0,[z0,z9,z357,z15,z5,z6]),(0,[z1219,z9,z3,z4,z5,z6]),(0,[z0,z9,z17,z4,z331,z6]),(0,[z0,z9,z4,z15,z5,z1181]),(0,[z332,z9,z17,z4,z5,z6]),(0,[z1220,z0,z3,z4,z5,z6])],[(0,[z0,z1221,z3,z4,z5,z6]),(0,[z43,z1,z3,z44,z5,z6]),(0,[z1222,z0,z3,z4,z5,z6]),(0,[z896,z0,z3,z4,z22,z5]),(0,[z38,z0,z4,z5,z177,z39]),(0,[z1182,z9,z4,z15,z5,z6]),(0,[z0,z334,z17,z4,z5,z6]),(0,[z0,z9,z4,z218,z6,z120]),(0,[z0,z9,z3,z5,z25,z853]),(0,[z0,z9,z4,z1223,z5,z6])],[(0,[z0,z9,z17,z628,z5,z6]),(0,[z0,z3,z175,z22,z5,z6]),(0,[z0,z336,z17,z4,z5,z6]),(0,[z8,z204,z3,z10,z5,z6]),(0,[z0,z9,z245,z4,z259,z6]),(0,[z0,z1224,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z1225]),(0,[z12,z0,z9,z3,z5,z13])],[(0,[z0,z9,z14,z4,z5,z6]),(0,[z0,z204,z14,z4,z5,z6]),(0,[z0,z3,z357,z22,z5,z6]),(0,[z0,z9,z1226,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z1151]),(0,[z113,z9,z17,z4,z5,z6]),(0,[z0,z9,z141,z3,z4,z120]),(0,[z130,z9,z3,z4,z122,z6]),(0,[z0,z3,z4,z1227,z5,z6])],[(0,[z9,z3,z4,z5,z1009,z6]),(0,[z581,z9,z3,z4,z35,z6]),(0,[z0,z9,z4,z15,z77,z6]),(0,[z0,z1,z3,z4,z5,z150]),(0,[z0,z3,z4,z5,z106,z34])],[(0,[z0,z9,z3,z4,z1228,z6]),(0,[z0,z9,z818,z4,z5,z6]),(0,[z0,z9,z3,z4,z1229,z6]),(0,[z0,z9,z1230,z4,z5,z6]),(0,[z0,z36,z4,z22,z5,z6]),(0,[z561,z0,z3,z22,z5,z6]),(0,[z0,z9,z4,z5,z93,z412]),(0,[z0,z99,z3,z4,z5,z6]),(0,[z0,z9,z4,z5,z6,z1231]),(0,[z0,z3,z4,z5,z106,z693]),(0,[z0,z9,z65,z4,z218,z6])]],
   [[(0,[z0,z1232,z3,z4,z5,z6]),(0,[z0,z3,z4,z22,z129,z6]),(0,[z0,z1,z904,z4,z5,z6]),(0,[z0,z3,z4,z887,z124,z6]),(0,[z0,z9,z17,z4,z174,z6]),(0,[z1233,z0,z3,z4,z5,z6])],[(0,[z507,z9,z3,z4,z35,z6]),(0,[z0,z336,z3,z4,z259,z6]),(0,[z0,z3,z4,z22,z77,z6]),(0,[z0,z1,z4,z161,z5,z6]),(0,[z0,z1,z162,z4,z5,z6]),(0,[z0,z17,z4,z66,z5,z6]),(0,[z0,z1234,z3,z4,z5,z6]),(0,[z1235,z0,z9,z4,z5,z6])],[(0,[z0,z9,z3,z4,z1236,z6]),(0,[z0,z9,z3,z1237,z5,z6]),(0,[z0,z9,z36,z4,z5,z6]),(0,[z0,z14,z4,z22,z5,z6]),(0,[z1238,z0,z3,z4,z5,z6]),(0,[z96,z0,z242,z4,z5,z6]),(0,[z0,z9,z4,z570,z5,z6]),(0,[z0,z1239,z3,z4,z5,z6])],[(0,[z0,z9,z3,z4,z1202,z6]),(0,[z0,z9,z3,z4,z5,z42]),(0,[z0,z372,z4,z22,z5,z6]),(0,[z0,z1240,z3,z4,z5,z6]),(0,[z0,z151,z4,z15,z5,z6]),(0,[z353,z9,z17,z4,z5,z6]),(0,[z0,z151,z3,z4,z5,z31]),(0,[z0,z9,z100,z4,z174,z6])],[(0,[z0,z9,z3,z4,z1241,z6]),(0,[z27,z0,z17,z4,z124,z6]),(0,[z1041,z9,z3,z4,z5,z6]),(0,[z0,z9,z65,z4,z218,z237])],[(0,[z0,z9,z3,z4,z5,z1242]),(0,[z0,z9,z14,z4,z5,z157]),(0,[z0,z9,z1243,z4,z5,z6]),(0,[z38,z0,z3,z4,z5,z878]),(0,[z0,z420,z4,z15,z5,z6]),(0,[z0,z279,z3,z91,z5,z25])],[(0,[z146,z144,z3,z4,z133,z6]),(0,[z64,z0,z1,z3,z270,z4]),(0,[z0,z1244,z3,z4,z5,z6]),(0,[z1245,z0,z9,z4,z5,z6])],[(0,[z567,z0,z32,z4,z5,z6]),(0,[z0,z1,z183,z4,z5,z6]),(0,[z1104,z0,z9,z4,z5,z6])]],
   [[(0,[z0,z3,z4,z1246,z5,z6]),(0,[z55,z9,z17,z4,z35,z6]),(0,[z0,z9,z1175,z4,z15,z5])],[(0,[z0,z9,z1247,z4,z5,z6]),(0,[z1248,z0,z9,z3,z4,z6]),(0,[z0,z9,z3,z4,z5,z1249]),(0,[z118,z0,z3,z4,z326,z6]),(0,[z223,z0,z1,z4,z5,z6]),(0,[z0,z9,z4,z5,z1111,z6]),(0,[z302,z0,z579,z15,z5,z6])],[(0,[z0,z9,z531,z4,z5,z93]),(0,[z0,z919,z3,z4,z5,z6]),(0,[z1250,z9,z3,z4,z5,z6]),(0,[z1251,z9,z3,z4,z5,z6]),(0,[z0,z9,z4,z752,z49,z6]),(0,[z558,z0,z9,z3,z5,z13]),(0,[z0,z9,z91,z570,z5,z25])],[(0,[z0,z9,z3,z4,z1252,z6]),(0,[z722,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z1253,z5,z6]),(0,[z0,z9,z1254,z4,z5,z6]),(0,[z0,z9,z4,z5,z1255,z6]),(0,[z0,z9,z1256,z4,z5,z6]),(0,[z0,z84,z3,z4,z5,z6])],[(0,[z0,z9,z3,z6,z712,z74])],[(0,[z0,z9,z1257,z4,z5,z6]),(0,[z0,z1258,z3,z4,z5,z6]),(0,[z64,z0,z3,z270,z4,z22]),(0,[z0,z3,z4,z22,z254,z6]),(0,[z0,z9,z680,z15,z5,z6]),(0,[z0,z9,z17,z4,z115,z6]),(0,[z20,z0,z9,z4,z5,z198]),(0,[z318,z9,z367,z4,z5,z6])],[(0,[z9,z3,z4,z876,z5,z6]),(0,[z0,z9,z17,z4,z381,z6]),(0,[z0,z3,z4,z5,z887,z6]),(0,[z0,z1259,z3,z4,z5,z6]),(0,[z0,z99,z4,z15,z5,z6]),(0,[z0,z9,z516,z3,z4,z58])],[(0,[z0,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z1260]),(0,[z0,z9,z3,z4,z1189,z6]),(0,[z0,z159,z3,z4,z5,z106]),(0,[z0,z3,z4,z5,z6,z1261])]],
   [[(0,[z0,z9,z3,z1262,z5,z6]),(0,[z287,z0,z4,z5,z93,z6]),(0,[z8,z3,z10,z22,z5,z6]),(0,[z0,z9,z1263,z4,z5,z6]),(0,[z0,z9,z3,z539,z5,z25]),(0,[z0,z3,z4,z22,z5,z186]),(0,[z273,z0,z4,z22,z5,z6]),(0,[z0,z9,z580,z15,z5,z6]),(0,[z0,z9,z65,z4,z198,z6]),(0,[z0,z9,z100,z4,z115,z6])],[(0,[z0,z9,z3,z4,z1264,z6]),(0,[z0,z62,z4,z5,z6,z406]),(0,[z0,z3,z4,z22,z1228,z6]),(0,[z0,z1,z3,z680,z5,z6]),(0,[z0,z1,z3,z4,z5,z34]),(0,[z0,z9,z1265,z4,z5,z6])],[(0,[z0,z9,z4,z15,z5,z42]),(0,[z0,z9,z3,z4,z1009,z6]),(0,[z76,z9,z3,z4,z77,z56]),(0,[z1266,z0,z9,z3,z4,z6]),(0,[z0,z9,z3,z4,z5,z1267]),(0,[z302,z0,z9,z775,z5,z6]),(0,[z223,z0,z4,z5,z6,z152])],[(0,[z0,z9,z17,z4,z396,z6]),(0,[z0,z9,z3,z4,z6,z1268]),(0,[z452,z3,z4,z374,z5,z6]),(0,[z0,z1,z3,z685,z5,z6]),(0,[z173,z0,z1,z3,z4,z6]),(1,[z0,z3,z4,z5,z878]),(0,[z0,z9,z448,z15,z5,z6])],[(0,[z51,z2,z135,z4,z5,z6]),(0,[z0,z9,z17,z221,z5,z6]),(0,[z0,z65,z4,z22,z218,z6])],[(0,[z0,z3,z4,z22,z5,z42]),(0,[z0,z4,z66,z15,z5,z6]),(0,[z173,z0,z9,z141,z4,z93])],[(0,[z0,z9,z4,z5,z1269,z6]),(0,[z130,z9,z3,z4,z5,z6]),(0,[z0,z206,z4,z605,z5,z6]),(0,[z0,z3,z4,z22,z1241,z6]),(0,[z0,z9,z4,z1270,z5,z6]),(0,[z0,z9,z1271,z4,z5,z6])],[(0,[z9,z21,z818,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z157]),(0,[z0,z9,z3,z4,z751,z6]),(0,[z0,z206,z881,z4,z5,z6]),(0,[z0,z1,z141,z4,z5,z93]),(0,[z250,z0,z3,z4,z5,z39]),(0,[z0,z9,z131,z4,z5,z6]),(0,[z0,z9,z17,z4,z5,z237]),(0,[z0,z9,z65,z3,z4,z237])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 509) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 509).take 515) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1024).take 365) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1389)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [509, 515, 365] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 91).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 91).take 93).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 184).take 72).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [91, 93, 72] = true :=
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

end PEqualNP.Outside.L_meta_37857

theorem PEqualNP.Outside.L_meta_37857 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074664 * 2 ^ 32 + 4274833608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074664 * 2 ^ 32 + 4274833608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_37857.solve