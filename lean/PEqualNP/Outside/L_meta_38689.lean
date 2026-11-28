import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38689

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
  Nat.testBit (4276808392 * 2 ^ 32 + 4241017032) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x800466338f1118c5#64 ++ 0x2001198ce3c44631#64 ++ 0x600cfe7f9f1139cf#64 ++ 0xd8033f9fe7c44e73#64 : BitVec 256),
   (0x0031108830066318#64 ++ 0x400c44220c0198c6#64 ++ 0xec731188f81fffff#64 ++ 0xbb1cc4623e07ffff#64 : BitVec 256),
   (0x0182e170c3618c61#64 ++ 0x8060b85c30d86318#64 ++ 0xf783e1f0e7e1ce73#64 ++ 0x7de0f87c39f8739c#64 : BitVec 256),
   (0x06dc01dd05ba0f82#64 ++ 0x01b70077416e83e0#64 ++ 0xfffc01ff07fe0f82#64 ++ 0xffff007fc1ff83e0#64 : BitVec 256),
   (0x0b6fba0006ddf000#64 ++ 0x02dbee8001b77c00#64 ++ 0xfffffe0007fff001#64 ++ 0xffffff8001fffc00#64 : BitVec 256),
   (0x13fbddeef8000000#64 ++ 0x04fef77bbe000000#64 ++ 0xdbfffffff8000003#64 ++ 0xf6fffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [7, 3]⟩, ⟨.or, [8, 1]⟩, ⟨.or, [9, 2]⟩, ⟨.and, [9, 6]⟩, ⟨.and, [10, 3]⟩, ⟨.or, [7, 12]⟩, ⟨.and, [13, 4]⟩, ⟨.or, [11, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0031108830066318 0x400c44220c0198c6 0xec731188f81fffff 0xbb1cc4623e07ffff

def z1 : W := mkw 0x0182c160c0000000 0x0060b05830000000 0x1380e07000000000 0x44e0381c00000000

def z2 : W := mkw 0x0182e170c3618c61 0x8060b85c30d86318 0xf783e1f0e7e1ce73 0x7de0f87c39f8739c

def z3 : W := mkw 0x06dc01dd05ba0f82 0x01b70077416e83e0 0xfffc01ff07fe0f82 0xffff007fc1ff83e0

def z4 : W := mkw 0x0b6fba0006ddf000 0x02dbee8001b77c00 0xfffffe0007fff001 0xffffff8001fffc00

def z5 : W := mkw 0x13fbddeef8000000 0x04fef77bbe000000 0xdbfffffff8000003 0xf6fffffffe000000

def z6 : W := mkw 0x800466338f1118c5 0x2001198ce3c44631 0x600cfe7f9f1139cf 0xd8033f9fe7c44e73

def z7 : W := mkw 0x0021100030046018 0x400844000c011806 0x00031000f801f07d 0x0000c4003e007c1f

def z8 : W := mkw 0x80042211071118c5 0x2001088441c44631 0x20000000071139cc 0x0800000001c44e73

def z9 : W := mkw 0x13fbddeef8046000 0x04fef77bbe011800 0xfffffffff81ff003 0xfffffffffe07fc00

def z10 : W := mkw 0x808467738f311cc5 0x202119dce3cc4731 0xf78cffff9ff13fcf 0xfde33fffe7fc4ff3

def z11 : W := mkw 0x0004000104100080 0x0001000041040020 0x000c000f00100180 0x80030003c0040060

def z12 : W := mkw 0x13fbddeef8000000 0x04fef77bbe000000 0x9bf3ff80f8000001 0x26fcffe03e000000

def z13 : W := mkw 0x036b980000000000 0x00dae60000000000 0xdbfffe0000000001 0xf6ffff8000000000

def z14 : W := mkw 0x1bffffeefeddf000 0x06fffffbbfb77c00 0xfffffffffffff003 0xfffffffffffffc00

def z15 : W := mkw 0x0b4eaa0006d99000 0x02d3aa8001b66400 0x138cee0007e00000 0x44e33b8001f80000

def z16 : W := mkw 0x0182e170c3618c61 0x8060b85c30d86318 0x3780e07007e1ce70 0x4de0381c01f8739c

def z17 : W := mkw 0x027d1088349e6318 0x409f44220d2798c6 0xffff1188ffffffff 0xffffc4623fffffff

def z18 : W := mkw 0x02d801cc00020300 0x00b60073000080c0 0xfffc01ff001e0f82 0xffff007fc00783e0

def z19 : W := mkw 0x0a6d3a0006ddf000 0x029b4e8001b77c00 0x2c7c1e0007fff000 0x8b1f078001fffc00

def z20 : W := mkw 0x0021100030046018 0x400844000c011806 0xec731000f81ff07d 0xbb1cc4003e07fc1f

def z21 : W := mkw 0x86dc67ff8fbb1fc7 0x21b719ffe3eec7f1 0xfffcffff9fff3fcf 0xffff3fffe7ffcff3

def z22 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z23 : W := mkw 0x1123dc22f8046018 0x4448f708be011806 0x0003fe00f801f07d 0x0000ff803e007c1f

def z24 : W := mkw 0x13fbddeef8066318 0x44fef77bbe0198c6 0xfffffffff81fffff 0xfffffffffe07ffff

def z25 : W := mkw 0x0923ba000245f000 0x0248ee8000917c00 0x0003fe000001f001 0x0000ff8000007c00

def z26 : W := mkw 0x13cacd66c8000000 0x04f2b359b2000000 0x138cee7700000000 0x44e33b9dc0000000

def z27 : W := mkw 0x065c008d049a0382 0x01970023412680e0 0x087c000f001e0180 0x821f0003c0078060

def z28 : W := mkw 0x8186e773cf719ce5 0xa061b9dcf3dc6739 0xf78ffffffff1ffff 0xfde3fffffffc7fff

def z29 : W := mkw 0x0000201003618c61 0x8000080400d86318 0x2400000007e1ce70 0x0900000001f8739c

def z30 : W := mkw 0x8035168b3c16739c 0x600d45a2cf059ce7 0xec7f1f8ff81fffff 0xbb1fc7e3fe07ffff

def z31 : W := mkw 0x0182e572cb618c61 0x8060b95cb2d86318 0xf78fffffffe1ce73 0xfde3fffffff8739c

def z32 : W := mkw 0x0031108830066318 0x400c44220c0198c6 0x08700000000e0000 0x021c000000038000

def z33 : W := mkw 0x800466238e1110c5 0x20011988e3844431 0x000cfe0f981131cd 0x80033f83e6044c73

def z34 : W := mkw 0x10004422f8000000 0x04001108be000000 0x00000000f8000000 0x000000003e000000

def z35 : W := mkw 0x8000442288000045 0x20001108a2000011 0x000000009800004c 0x0000000026000013

def z36 : W := mkw 0x092398000044e000 0x0248e60000113800 0x000300000000c000 0x0000c00000003000

def z37 : W := mkw 0x0000442288000000 0x00001108a2000000 0x000cee7700000000 0x40033b9dc0000000

def z38 : W := mkw 0x0000442288000000 0x00001108a2000000 0x400cfe7f98000003 0xd0033f9fe6000000

def z39 : W := mkw 0x0010008830020318 0x400400220c0080c6 0x00000188f8000ffe 0x000000623e0003ff

def z40 : W := mkw 0x0080015001200c00 0x0020005400480300 0xf78001f007e00e02 0x7de0007c01f80380

def z41 : W := mkw 0x0000000000066318 0x40000000000198c6 0x24000000001ffffc 0x090000000007ffff

def z42 : W := mkw 0x003170b8b3076b59 0x400c5c2e2cc1dad6 0xec73f1f8ff1fffff 0xfb1cfc7e3fc7ffff

def z43 : W := mkw 0x0182a15043618c61 0x8060a85410d86318 0xb783018067e1ce70 0x2de0c06019f8739c

def z44 : W := mkw 0x0004001105100880 0x0001000441440220 0x2000000007100980 0x0800000001c40260

def z45 : W := mkw 0x07cee175c7f98ce3 0x81f3b85d71fe6338 0x138ce07707e00000 0x44e3381dc1f80000

def z46 : W := mkw 0x8106e633cf5198e5 0xa041b98cf3d46639 0x600ffe7fff11f9ff 0xd803ff9fffc47e7f

def z47 : W := mkw 0x0080015001200c00 0x0020005400480300 0x1380007007e00000 0x44e0001c01f80000

def z48 : W := mkw 0x0000000000000000 0x0000000000000000 0x60001008981139cf 0x9800040226044e73

def z49 : W := mkw 0x803576bbbf177bdd 0x600d5daeefc5def7 0xec7fffffff1fffff 0xfb1fffffffc7ffff

def z50 : W := mkw 0x003154aab8000000 0x000c552aae000000 0xc87ffffff8000003 0xf21ffffffe000000

def z51 : W := mkw 0x049001dd01220f82 0x01240077404883e0 0x000001ff00000f82 0x0000007fc00003e0

def z52 : W := mkw 0x0a6d1a00049c7000 0x029b468001271c00 0x087c1e00001e3000 0x821f078000078c00

def z53 : W := mkw 0x800066228a011045 0x20001988a2804411 0x0000fe009801304d 0x00003f8026004c13

def z54 : W := mkw 0x0404001105ba0f82 0x01010004416e83e0 0x2400000007fe0f80 0x0900000001ff83e0

def z55 : W := mkw 0x1123dc22f8000000 0x0448f708be000000 0x0003fe00f8000001 0x0000ff803e000000

def z56 : W := mkw 0x06dc45ff8dba0f82 0x01b7117fe36e83e0 0xfffcffff9ffe0f83 0xffff3fffe7ff83e0

def z57 : W := mkw 0x13fbfdfefb618c61 0x84feff7fbed86318 0xffffffffffe1ce73 0xfffffffffff8739c

def z58 : W := mkw 0x0004221107111880 0x0001088441c44620 0x600cfe7f07113983 0xd8033f9fc1c44e60

def z59 : W := mkw 0x06d801cc00aa0702 0x01b60073002a81c0 0xdffc01ff00ee0602 0xf7ff007fc03b8180

def z60 : W := mkw 0x800466338f1118c5 0x2001198ce3c44631 0xe40fffffff11ffff 0xf903ffffffc47fff

def z61 : W := mkw 0x0182814040608420 0x8060a05010182108 0x9783018060e0c630 0x25e0c0601838318c

def z62 : W := mkw 0x0182e170c3618c61 0x8060b85c30d86318 0x1380e07007e00000 0x44e0381c01f80000

def z63 : W := mkw 0x0102a00002418000 0x0040a80000906000 0xf783e00007e1c001 0x7de0f80001f87000

def z64 : W := mkw 0x0beffb70c7fdfc61 0x82fbfedc31ff7f18 0xfffffff0e7fffe73 0xfffffffc39ffff9c

def z65 : W := mkw 0x0fff99dd05feef82 0x03ffe677417fbbe0 0xffff01ff07fecf82 0xffffc07fc1ffb3e0

def z66 : W := mkw 0x0000000000000000 0x0000000000000000 0xe40300000001c001 0x3900c00000007000

def z67 : W := mkw 0x0804220006d99000 0x0201088001b66400 0x0000000007e00000 0x0000000001f80000

def z68 : W := mkw 0x13fbddeef8000000 0x04fef77bbe000000 0xfbfffffff81139cf 0xfefffffffe044e73

def z69 : W := mkw 0x0031108830066318 0x400c44220c0198c6 0x8c730180600ec630 0x231cc0601803b18c

def z70 : W := mkw 0x13fbddeef8066318 0x44fef77bbe0198c6 0xdffffffff80ec633 0xf7fffffffe03b18c

def z71 : W := mkw 0x0084015105300c80 0x00210054414c0320 0xf78c01ff07f00f82 0xfde3007fc1fc03e0

def z72 : W := mkw 0x13fb99cc70000000 0x04fee6731c000000 0x9bf3018060000000 0x26fcc06018000000

def z73 : W := mkw 0x13fbddeef8000000 0x04fef77bbe000000 0x1bfcfe7f18000000 0xc6ff3f9fc6000000

def z74 : W := mkw 0x0804220006dff318 0x4201088001b7fcc6 0x2400000007fffffc 0x0900000001ffffff

def z75 : W := mkw 0x06dc01dd35ba0f9a 0x41b700774d6e83e6 0xfffc01fffffe0ffe 0xffff007fffff83ff

def z76 : W := mkw 0x06d801cc00aa0702 0x01b60073002a81c0 0xfff0018800fe0f82 0xbffc0062003f83e0

def z77 : W := mkw 0x0000000000608420 0x8000000000182108 0x0400000000e0c630 0x010000000038318c

def z78 : W := mkw 0x109045eef8000000 0x0424117bbe000000 0x400cfffff8000003 0xd0033ffffe000000

def z79 : W := mkw 0x0182c562c8000000 0x0060b158b2000000 0xd38ffffff8000003 0xf4e3fffffe000000

def z80 : W := mkw 0x0021100030066318 0x400844000c0198c6 0x24031000f81ffffd 0x0900c4003e07ffff

def z81 : W := mkw 0x0182e170c3618c61 0x8060b85c30d86318 0x9783e1f067e0c630 0x65e0f87c19f8318c

def z82 : W := mkw 0x80004433890008c5 0x2000110ce2400231 0x0000007f980009ce 0x0000001fe6000273

def z83 : W := mkw 0x9123fe22fa011045 0x2448ff88be804411 0x0003fe00f801304d 0x0000ff803e004c13

def z84 : W := mkw 0x0000000000000000 0x0000000000000000 0xe4030180e001ce73 0x3900c0603800739c

def z85 : W := mkw 0x067d108d349e639a 0x419f44234d2798e6 0x087c100f181e318c 0x821f0403c6078c63

def z86 : W := mkw 0x06f911cc30ae671a 0x41be44730c2b99c6 0x9ff3018060eec630 0x27fcc060183bb18c

def z87 : W := mkw 0x0a6d1a00049c7000 0x029b468001271c00 0xfffc1e0007fe3000 0xffff078001ff8c00

def z88 : W := mkw 0x000020100367ef79 0xc000080400d9fbde 0x2400000007fffffc 0x0900000001ffffff

def z89 : W := mkw 0x0000000000066318 0x40000000000198c6 0x00000000001e318c 0x0000000000078c63

def z90 : W := mkw 0x1192c5eef8000000 0x0464b17bbe000000 0xd383e1fff8000003 0x74e0f87ffe000000

def z91 : W := mkw 0x0fffbbdd07ffff82 0x03ffeef741ffffe0 0xffffffff07ffff83 0xffffffffc1ffffe0

def z92 : W := mkw 0x0b6fba0036ddf018 0x42dbee800db77c06 0xfffffe00fffff07d 0xffffff803ffffc1f

def z93 : W := mkw 0x06cc015505ba0f82 0x01b30055416e83e0 0x378c007707fe0f80 0x4de3001dc1ff83e0

def z94 : W := mkw 0x0031108830000000 0x000c44220c000000 0xc8731188f8000003 0xb21cc4623e000000

def z95 : W := mkw 0x80042211071118c5 0x2001088441c44631 0x0000000007000000 0x0000000001c00000

def z96 : W := mkw 0x0031108830066318 0x400c44220c0198c6 0xec731008181ff18d 0xbb1cc4020607fc63

def z97 : W := mkw 0x0004020004101000 0x0001008001040400 0x000c1e0000103000 0x8003078000040c00

def z98 : W := mkw 0x824c66338f9918c5 0x2093198ce3e64631 0xfffcfe7f9fff39cf 0xffff3f9fe7ffce73

def z99 : W := mkw 0x024c000004980000 0x0093000001260000 0xfffc000007fe0000 0xffff000001ff8000

def z100 : W := mkw 0x064c001105ba0f82 0x01930004416e83e0 0xfffc000007fe0f80 0xffff000001ff83e0

def z101 : W := mkw 0x927d1e8f3c101084 0x249f47a3cf040421 0x087c1e0f1810318c 0x821f0783c6040c63

def z102 : W := mkw 0x036b980000046000 0x00dae60000011800 0xfffffe00001ff001 0xffffff800007fc00

def z103 : W := mkw 0x0031108830066318 0x400c44220c0198c6 0x08701008181e318c 0x821c040206078c63

def z104 : W := mkw 0x13fbddeef8066318 0x44fef77bbe0198c6 0xdbfffffff81e318f 0xf6fffffffe078c63

def z105 : W := mkw 0x06cc015505b80c82 0x01b30055416e0320 0x138c007707e00000 0x44e3001dc1f80000

def z106 : W := mkw 0x0004220006111000 0x0001088001844400 0x600cfe0007113001 0xd8033f8001c44c00

def z107 : W := mkw 0x0923ba000245f000 0x0248ee8000917c00 0xec73fe00001ff001 0xbb1cff800007fc00

def z108 : W := mkw 0x0b6fba0006ddf000 0x02dbee8001b77c00 0x9fffee0007eec000 0x67fffb8001fbb000

def z109 : W := mkw 0x0ffffbfdc7ffffe3 0x83fffeff71fffff8 0xffffffffe7fffff3 0xfffffffff9fffffc

def z110 : W := mkw 0x8004221107719ce5 0xa001088441dc6739 0x2400000007f1fffc 0x0900000001fc7fff

def z111 : W := mkw 0x049401dd05320f82 0x01250077414c83e0 0x600c01ff07100f82 0xd803007fc1c403e0

def z112 : W := mkw 0x1923fe22fa45f000 0x0648ff88be917c00 0x0003fe00f801f001 0x0000ff803e007c00

def z113 : W := mkw 0x0102800000000000 0x0040a00000000000 0xd383e00000000001 0x74e0f80000000000

def z114 : W := mkw 0x0182e170c3618c61 0x8060b85c30d86318 0x0003e1f0e001ce73 0x0000f87c3800739c

def z115 : W := mkw 0x08040200049c7000 0x0201008001271c00 0x00000000001e3000 0x0000000000078c00

def z116 : W := mkw 0x1192e5fefb618c61 0x8464b97fbed86318 0xf783e1ffffe1ce73 0x7de0f87ffff8739c

def z117 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000180e0000e72 0x000000603800039c

def z118 : W := mkw 0x064c000504980082 0x0193000141260020 0x000c000700000000 0x00030001c0000000

def z119 : W := mkw 0x0192e1f8f3638f79 0xc064b87e3cd8e3de 0xf783e1f8ffe1cfff 0x7de0f87e3ff873ff

def z120 : W := mkw 0x8a6d7e338f9d78c5 0x229b5f8ce3e75e31 0x687cfe7f9f1f39cf 0xda1f3f9fe7c7ce73

def z121 : W := mkw 0x800406030c101084 0x20010180c3040421 0x000c1e0f1810318c 0x80030783c6040c63

def z122 : W := mkw 0x10b155eef8066318 0x442c557bbe0198c6 0xec7311fff81fffff 0xbb1cc47ffe07ffff

def z123 : W := mkw 0x01b3f1f8f367ef79 0xc06cfc7e3cd9fbde 0xfff3f1f8ffffffff 0xfffcfc7e3fffffff

def z124 : W := mkw 0x0021100000046000 0x0008440000011800 0xec731000001ff001 0xbb1cc4000007fc00

def z125 : W := mkw 0x1279188c30000000 0x049e46230c000000 0x0870000000000000 0x021c000000000000

def z126 : W := mkw 0x024c001105980880 0x0093000441660220 0xfffc007f07fe0982 0xffff001fc1ff8260

def z127 : W := mkw 0x8b6ffe338fddf8c5 0x22dbff8ce3f77e31 0xfffffe7f9ffff9cf 0xffffff9fe7fffe73

def z128 : W := mkw 0x93ffffffff177bdd 0x64ffffffffc5def7 0xffffffffff1fffff 0xffffffffffc7ffff

def z129 : W := mkw 0x10804566c8000000 0x04201159b2000000 0x0000007700000000 0x0000001dc0000000

def z130 : W := mkw 0x0031108830000000 0x000c44220c000000 0xec731188f801ce73 0xbb1cc4623e00739c

def z131 : W := mkw 0x0400001101220f82 0x01000004404883e0 0x0000000000000f80 0x00000000000003e0

def z132 : W := mkw 0x0000220002011000 0x0000088000804400 0x0000fe0000013001 0x00003f8000004c00

def z133 : W := mkw 0x80042211071118c5 0x2001088441c44631 0x600c007f071139ce 0xd803001fc1c44e73

def z134 : W := mkw 0x0182e170c3618c61 0x8060b85c30d86318 0xf783e07007e1c001 0x7de0f81c01f87000

def z135 : W := mkw 0x06dc01dd05ba0f82 0x01b70077416e83e0 0x9ffc01f707ee0600 0x67ff007dc1fb8180

def z136 : W := mkw 0x0923fa20c245f061 0x8248fe8830917c18 0x0003fe00e001f071 0x0000ff8038007c1c

def z137 : W := mkw 0x80846773cf311ce5 0xa02119dcf3cc4739 0x600cffffff113fff 0xd8033fffffc44fff

def z138 : W := mkw 0x0beffb60c6ddf000 0x02fbfed831b77c00 0xfffffff0e7fff003 0xfffffffc39fffc00

def z139 : W := mkw 0x93ffffffff1118c5 0x24ffffffffc44631 0xfbffffffff1139cf 0xfeffffffffc44e73

def z140 : W := mkw 0x1133dcaaf8066318 0x444cf72abe0198c6 0xec73ff88f81fffff 0xbb1cffe23e07ffff

def z141 : W := mkw 0x0010008800000000 0x0004002200000000 0xc870018800000002 0xb21c006200000000

def z142 : W := mkw 0x07da81cc40ea8722 0x81f6a073103aa1c8 0x9ff3018060eec630 0x27fcc060183bb18c

def z143 : W := mkw 0x0035109935166b98 0x400d44264d459ae6 0xec7f11ffff1fffff 0xfb1fc47fffc7ffff

def z144 : W := mkw 0x003154aab8066318 0x400c552aae0198c6 0xec7ffffff81fffff 0xfb1ffffffe07ffff

def z145 : W := mkw 0x06dc01dd05ba0f82 0x01b70077416e83e0 0x1bfc007f07fe0180 0xc6ff001fc1ff8060

def z146 : W := mkw 0x0b6fba0006ddf000 0x02dbee8001b77c00 0xffffff80e7fffe73 0xffffffe039ffff9c

def z147 : W := mkw 0x02d801cc00000000 0x00b6007300000000 0xdbfc01ff00000002 0xf6ff007fc0000000

def z148 : W := mkw 0x0080617083210c41 0x0020185c20c84310 0xf780e1f087e10e43 0x7de0387c21f84390

def z149 : W := mkw 0x0000603083010841 0x0000180c20c04210 0xe403e1f0e701ce73 0x7900f87c39c0739c

def z150 : W := mkw 0x800466338f1118c5 0x2001198ce3c44631 0x000cee7707000000 0x40033b9dc1c00000

def z151 : W := mkw 0x0031108830066318 0x400c44220c0198c6 0x08701188f81e3ffe 0x821c04623e078fff

def z152 : W := mkw 0x00804170c1200c61 0x8020105c30480318 0xf78001f0e7e00e72 0x7de0007c39f8039c

def z153 : W := mkw 0x02f911cc30066318 0x40be44730c0198c6 0xffff11fff81fffff 0xffffc47ffe07ffff

def z154 : W := mkw 0x0000000000000000 0x0000000000000000 0x6000100000113001 0x9800040000044c00

def z155 : W := mkw 0x0b4a880000c88000 0x02d2a20000322000 0x1380000000e00000 0x04e0000000380000

def z156 : W := mkw 0x0080014000200400 0x0020005000080100 0x9780018000e00600 0x25e0006000380180

def z157 : W := mkw 0x93ffffffff719ce5 0xa4ffffffffdc6739 0xfffffffffff1ffff 0xfffffffffffc7fff

def z158 : W := mkw 0x8804221107ddf8c5 0x2201088441f77e31 0x2400000007fff9cc 0x0900000001fffe73

def z159 : W := mkw 0x17ff99dd75ba0f82 0x05ffe6775d6e83e0 0xffff01ff67fe0f82 0xffffc07fd9ff83e0

def z160 : W := mkw 0x0804220006ddf000 0x0201088001b77c00 0x640cfe0007fff001 0xd9033f8001fffc00

def z161 : W := mkw 0x06fd11dd35be6f9a 0x41bf44774d6f9be6 0xffff11ffffffffff 0xffffc47fffffffff

def z162 : W := mkw 0x1bffffeefedff318 0x46fffffbbfb7fcc6 0xffffffffffffffff 0xffffffffffffffff

def z163 : W := mkw 0x12791c8e38066318 0x449e47238e0198c6 0x087c1e0f181e318c 0x821f0783c6078c63

def z164 : W := mkw 0x049041fdc1220fe3 0x8124107f704883f8 0x000001ffe0000ff2 0x0000007ff80003fc

def z165 : W := mkw 0x12f91dce38000000 0x04be47738e000000 0xdbfc1fff18000002 0xf6ff07ffc6000000

def z166 : W := mkw 0x800406130d101884 0x20010184c3440621 0x600c1e7f1f10398e 0xd803079fc7c40e63

def z167 : W := mkw 0x13cacd66c8000000 0x04f2b359b2000000 0xd38feff7e0000003 0x74e3fbfdf8000000

def z168 : W := mkw 0x0010008800020300 0x00040022000080c0 0xec700188001e0f82 0xbb1c0062000783e0

def z169 : W := mkw 0x0b6fba0006ddf000 0x02dbee8001b77c00 0x138ffe0007e1f001 0x44e3ff8001f87c00

def z170 : W := mkw 0x0000000000046000 0x0000000000011800 0x24000000001ff000 0x090000000007fc00

def z171 : W := mkw 0x880466338fddf8c5 0x2201198ce3f77e31 0x640cfe7f9ffff9cf 0xd9033f9fe7fffe73

def z172 : W := mkw 0x0b4eaa0006d99000 0x02d3aa8001b66400 0xfffcee0007fe0000 0xffff3b8001ff8000

def z173 : W := mkw 0x0b6b980000cce000 0x02dae60000333800 0x9ff3000000eec000 0x27fcc000003bb000

def z174 : W := mkw 0x00804170c1200c61 0x8020105c30480318 0x000001f0e0000e72 0x0000007c3800039c

def z175 : W := mkw 0x0a691800008c6000 0x029a460000231800 0x08700000000e0000 0x021c000000038000

def z176 : W := mkw 0x0182814040000000 0x0060a05010000000 0x9383018060000000 0x24e0c06018000000

def z177 : W := mkw 0x17fbddfff9220f82 0x05fef77ffe4883e0 0xdbfffffff8000f83 0xf6fffffffe0003e0

def z178 : W := mkw 0x13fbddeef8020318 0x44fef77bbe0080c6 0xdbfffffff8000fff 0xf6fffffffe0003ff

def z179 : W := mkw 0x13fb99cc70066318 0x44fee6731c0198c6 0x9ff30180600ec630 0x27fcc0601803b18c

def z180 : W := mkw 0x01b3d1e8f0066318 0x406cf47a3c0198c6 0xfff3f1f8f81fffff 0xfffcfc7e3e07ffff

def z181 : W := mkw 0x0000000000000000 0x0000000000000000 0xe4031188f811ffff 0xb900c4623e047fff

def z182 : W := mkw 0x849045ff89220fc7 0x2124117fe24883f1 0x000001ff98000fce 0x0000007fe60003f3

def z183 : W := mkw 0x109045eef8000000 0x0424117bbe000000 0x000001fff8000002 0x0000007ffe000000

def z184 : W := mkw 0x0b7fba8836dff318 0x42dfeea20db7fcc6 0xffffff88ffffffff 0xffffffe23fffffff

def z185 : W := mkw 0x0b4eaa0006d99000 0x02d3aa8001b66400 0xf78fee0007e1c001 0x7de3fb8001f87000

def z186 : W := mkw 0x86dc07df0dba1f86 0x21b701f7c36e87e1 0xfffc1fff1ffe3f8e 0xffff07ffc7ff8fe3

def z187 : W := mkw 0x0004000004100000 0x0001000001040000 0x600c000007100000 0xd803000001c40000

def z188 : W := mkw 0x06dc01dd05ba0f82 0x01b70077416e83e0 0xffff01ffe7ffcff3 0xffffc07ff9fff3fc

def z189 : W := mkw 0x0102e03083418841 0x0040b80c20d06210 0xf783e07087e1c843 0x7de0f81c21f87210

def z190 : W := mkw 0x86cc67778fb91cc7 0x21b319dde3ee4731 0x738cfe7f9ff139cf 0xdce33f9fe7fc4e73

def z191 : W := mkw 0x0000603083010841 0x0000180c20c04210 0x6000e07087010843 0x5800381c21c04210

def z192 : W := mkw 0x13fb99cc70000000 0x04fee6731c000000 0xdbff01ff60000002 0xf6ffc07fd8000000

def z193 : W := mkw 0x06dc01dd05ba0f82 0x01b70077416e83e0 0x138c01ff07e00f82 0x44e3007fc1f803e0

def z194 : W := mkw 0x13fbddeef8608420 0x84fef77bbe182108 0xdffffffff8e0c633 0xf7fffffffe38318c

def z195 : W := mkw 0x1bfbffeefa45f000 0x06fefffbbe917c00 0xdbfffffff801f003 0xf6fffffffe007c00

def z196 : W := mkw 0x17ffddfffdba0f82 0x05fff77fff6e83e0 0xfffffffffffe0f83 0xffffffffffff83e0

def z197 : W := mkw 0x865c068f0c9a1386 0x219701a3c32684e1 0x087c1e0f181e318c 0x821f0783c6078c63

def z198 : W := mkw 0x1123dc22f8000000 0x0448f708be000000 0x400ffe7ff8000003 0xd003ff9ffe000000

def z199 : W := mkw 0x0035328836177318 0x400d4ca20d85dcc6 0xec7fff88ff1fffff 0xfb1fffe23fc7ffff

def z200 : W := mkw 0x13ebdd66f8000000 0x04faf759be000000 0x138ffe77f8000001 0x44e3ff9dfe000000

def z201 : W := mkw 0x0133b0883247e318 0x404cec220c91f8c6 0xfff3f188ffffffff 0xfffcfc623fffffff

def z202 : W := mkw 0x12791c8e38000000 0x049e47238e000000 0x087c1e0f18000000 0x821f0783c6000000

def z203 : W := mkw 0x0000000000066318 0x40000000000198c6 0xe4030180e01fffff 0x3900c0603807ffff

def z204 : W := mkw 0x0400000000aa0702 0x01000000002a81c0 0x0400000000ee0600 0x01000000003b8180

def z205 : W := mkw 0x86dc67ff8fbb1fc7 0x21b719ffe3eec7f1 0xfffcefff07fe0f82 0xffff3bffc1ff83e0

def z206 : W := mkw 0x8186e773cf1118c5 0x2061b9dcf3c44631 0xf38fffffff1139cf 0xfce3ffffffc44e73

def z207 : W := mkw 0x8000220002011045 0x2000088000804411 0x000000000001304c 0x0000000000004c13

def z208 : W := mkw 0x13dacdeec8000000 0x04f6b37bb2000000 0xdbfcefff00000002 0xf6ff3bffc0000000

def z209 : W := mkw 0x0000000000000000 0x0000000000000000 0xe400018000000e02 0x3900006000000380

def z210 : W := mkw 0x065c008d049a0382 0x01970023412680e0 0xec7c018f001e0f82 0xbb1f0063c00783e0

def z211 : W := mkw 0x800066228a011045 0x20001988a2804411 0x0000ee0000000000 0x00003b8000000000

def z212 : W := mkw 0x0182c160c0000000 0x0060b05830000000 0xf783e1f0e001ce73 0x7de0f87c3800739c

def z213 : W := mkw 0x80042211071118c5 0x2001088441c44631 0x600010089f1139cf 0x9800040227c44e73

def z214 : W := mkw 0x13cacd66c8000000 0x04f2b359b2000000 0x538cfe7f98000003 0xd4e33f9fe6000000

def z215 : W := mkw 0x93ceef77cf1118c5 0x24f3bbddf3c44631 0x738cfe7f9f1139cf 0xdce33f9fe7c44e73

def z216 : W := mkw 0x0efd1bdd05be7f82 0x03bf46f7416f9fe0 0xfffc1fff07fe3f82 0xffff07ffc1ff8fe0

def z217 : W := mkw 0x0182e160c2418000 0x0060b85830906000 0xf783e1f0e7e1c003 0x7de0f87c39f87000

def z218 : W := mkw 0x0010008800020300 0x00040022000080c0 0x8c700180000e0600 0x231c006000038180

def z219 : W := mkw 0x13dacdeef8000000 0x04f6b37bbe000000 0x138ceffff8000002 0x44e33bfffe000000

def z220 : W := mkw 0x0000001001000800 0x0000000400400200 0x6000007007000802 0x5800001c01c00200

def z221 : W := mkw 0x12795caeb8000000 0x049e572bae000000 0x487cfe7f98000003 0xd21f3f9fe6000000

def z222 : W := mkw 0x0182a14042618420 0x8060a85010986108 0xf783e18067e1c631 0x7de0f86019f8718c

def z223 : W := mkw 0x06d801cc00aa0702 0x01b60073002a81c0 0x9ff0018000ee0600 0x27fc0060003b8180

def z224 : W := mkw 0x1befff66ceddf000 0x06fbffd9b3b77c00 0xfffffe7707fff001 0xffffff9dc1fffc00

def z225 : W := mkw 0x13fbfdeefa418061 0x84feff7bbe906018 0xdbfffffff801c073 0xf6fffffffe00701c

def z226 : W := mkw 0x0404001105b80c82 0x01010004416e0320 0x0000000007e00000 0x0000000001f80000

def z227 : W := mkw 0x0000442288000000 0x00001108a2000000 0x600cfe7f981139cf 0xd8033f9fe6044e73

def z228 : W := mkw 0x08211a0000047000 0x0208468000011c00 0x00001e0000003000 0x0000078000000c00

def z229 : W := mkw 0x11a3fd72fb618c61 0x8468ff5cbed86318 0xf783fff0ffe1ce73 0x7de0fffc3ff8739c

def z230 : W := mkw 0x0021100030046018 0x400844000c011806 0x60031008f811f9ff 0x9800c4023e047e7f

def z231 : W := mkw 0x8b7ffebbbfdffbdd 0x62dfffaeeff7fef7 0xffffffffffffffff 0xffffffffffffffff

def z232 : W := mkw 0x13fbddeef8046018 0x44fef77bbe011806 0xdbfffffff801f07f 0xf6fffffffe007c1f

def z233 : W := mkw 0x0080015001200c00 0x0020005400480300 0x000001f000000e02 0x0000007c00000380

def z234 : W := mkw 0x0248000000880000 0x0092000000220000 0x9ff0000000ee0000 0x27fc0000003b8000

def z235 : W := mkw 0x036bb80002418000 0x00daee0000906000 0xfffffe0007e1c001 0xffffff8001f87000

def z236 : W := mkw 0x800466338f1118c5 0x2001198ce3c44631 0x000cfe7f1f10318c 0xc0033f9fc7c40c63

def z237 : W := mkw 0x0182e170c3618c61 0x8060b85c30d86318 0xf780e1f007e00e02 0x7de0387c01f80380

def z238 : W := mkw 0x0b6fba0006ddf000 0x02dbee8001b77c00 0x087ffe00001ff001 0x821fff800007fc00

def z239 : W := mkw 0x12791c8e38066318 0x449e47238e0198c6 0xec7f1f8ff81fffff 0xbb1fc7e3fe07ffff

def z240 : W := mkw 0x0031108830020300 0x000c44220c0080c0 0xec731188f81e0f83 0xbb1cc4623e0783e0

def z241 : W := mkw 0x13fbf9fcf3618c61 0x84fefe7f3cd86318 0xfff3e1f0e7e1ce73 0x7ffcf87c39f8739c

def z242 : W := mkw 0x0031108830000000 0x000c44220c000000 0x0870100818000000 0x821c040206000000

def z243 : W := mkw 0x0bceeb70c7f99c61 0x82f3badc31fe6718 0xf78feff0e7e1ce73 0x7de3fbfc39f8739c

def z244 : W := mkw 0x849467ff8f331fc7 0x212519ffe3ccc7f1 0x600cffff9f113fcf 0xd8033fffe7c44ff3

def z245 : W := mkw 0x13fbddeef8000000 0x04fef77bbe000000 0xfffffffff801ce73 0xfffffffffe00739c

def z246 : W := mkw 0x802576338f1578c5 0x20095d8ce3c55e31 0xec7ffe7f9f1ff9cf 0xfb1fff9fe7c7fe73

def z247 : W := mkw 0x12480c0608000000 0x0492030182000000 0x000c0e0700000000 0x00030381c0000000

def z248 : W := mkw 0x13fbddeef8000000 0x04fef77bbe000000 0x9bffeff760000000 0x66fffbfdd8000000

def z249 : W := mkw 0x07dee1fdc7fb8fe3 0x81f7b87f71fee3f8 0xffffe1ffe7ffcff3 0xfffff87ff9fff3fc

def z250 : W := mkw 0x8b6fbe030eddf084 0x22dbef80c3b77c21 0xfffffe0f1ffff18d 0xffffff83c7fffc63

def z251 : W := mkw 0x0031108830066318 0x400c44220c0198c6 0xcc731188f80ec633 0xb31cc4623e03b18c

def z252 : W := mkw 0x0182c160c0608420 0x8060b05830182108 0xd783e1f0e0e0c633 0x75e0f87c3838318c

def z253 : W := mkw 0x0000603083010841 0x0000180c20c04210 0x0000e07007000000 0x4000381c01c00000

def z254 : W := mkw 0x0102e020c2418061 0x8040b80830906018 0x0003e000e001c071 0x0000f8003800701c

def z255 : W := mkw 0x06dc21dd07fb8fe3 0x81b7087741fee3f8 0xfffc01ff07ffcff2 0xffff007fc1fff3fc

def z256 : W := mkw 0x93ffdfeffc101084 0x24fff7fbff040421 0xdbfffffff810318f 0xf6fffffffe040c63

def z257 : W := mkw 0x024c220006991000 0x0093088001a64400 0xfffcfe0007ff3001 0xffff3f8001ffcc00

def z258 : W := mkw 0x06dc01cc04ba0702 0x01b70073012e81c0 0xfffc018007fe0600 0xffff006001ff8180

def z259 : W := mkw 0x0102e020c2418061 0x8040b80830906018 0x0000e00000000000 0x0000380000000000

def z260 : W := mkw 0x0182e170c3618c61 0x8060b85c30d86318 0x1380e1f0e7e00e72 0x44e0387c39f8039c

def z261 : W := mkw 0x0825320006ddf000 0x02094c8001b77c00 0xec73100007fff001 0xbb1cc40001fffc00

def z262 : W := mkw 0x97ffffffffbb1fc7 0x25ffffffffeec7f1 0xffffffffffff3fcf 0xffffffffffffcff3

def z263 : W := mkw 0x06cc015505b80c82 0x01b30055416e0320 0xfffc007707fe0000 0xffff001dc1ff8000

def z264 : W := mkw 0x803576bbbf1118c5 0x200d5daeefc44631 0xe87fffffff1139cf 0xfa1fffffffc44e73

def z265 : W := mkw 0x0182c170c1608c61 0x8060b05c30582318 0x978301f0e0e0ce72 0x25e0c07c3838339c

def z266 : W := mkw 0x0bebf970c3edec61 0x82fafe5c30fb7b18 0xfff3e1f0e7efce73 0x7ffcf87c39fbf39c

def z267 : W := mkw 0x0031108830020318 0x400c44220c0080c6 0xc8731188f8000fff 0xb21cc4623e0003ff

def z268 : W := mkw 0x06dc01dd05ba0f82 0x01b70077416e83e0 0xfffc11ff9fff3fcf 0xffff047fe7ffcff3

def z269 : W := mkw 0x0b6f9a00049c7000 0x02dbe68001271c00 0xdbfffe00001e3001 0xf6ffff8000078c00

def z270 : W := mkw 0x000444338d100880 0x0001110ce3440220 0x600cfe7f9f100983 0xd8033f9fe7c40260

def z271 : W := mkw 0x1bfbddeef8cce000 0x06fef77bbe333800 0xdffffffff8eec003 0xf7fffffffe3bb000

def z272 : W := mkw 0x0000000000000000 0x0000000000000000 0x000010081810318c 0x8000040206040c63

def z273 : W := mkw 0x0000000000000000 0x0000000000000000 0x20000000001139cc 0x0800000000044e73

def z274 : W := mkw 0x1123fc22fa418061 0x8448ff08be906018 0x0003fe00f801c071 0x0000ff803e00701c

def z275 : W := mkw 0x00046031871108c1 0x0001180c61c44230 0x600ce07f871109c3 0xd803381fe1c44270

def z276 : W := mkw 0x02d845ee88000000 0x00b6117ba2000000 0xdbfcffff98000003 0xf6ff3fffe6000000

def z277 : W := mkw 0x0031108830066318 0x400c44220c0198c6 0x8c730188f80ecffe 0x231cc0623e03b3ff

def z278 : W := mkw 0x00b111d831266f18 0x402c44760c499bc6 0xfff311f8ffffffff 0xfffcc47e3fffffff

def z279 : W := mkw 0x03ebd960c0000000 0x00faf65830000000 0xdbfffff0e0000003 0xf6fffffc38000000

def z280 : W := mkw 0x0804220006ddf000 0x0201088001b77c00 0x2400000007fff000 0x0900000001fffc00

def z281 : W := mkw 0x00004020c0000061 0x8000100830000018 0x00000000e0000070 0x000000003800001c

def z282 : W := mkw 0x13ffffeefe111000 0x04fffffbbf844400 0xfbffffffff113003 0xfeffffffffc44c00

def z283 : W := mkw 0x86dc23dd07bb1fc7 0x21b708f741eec7f1 0xfffc01ff07ff3fce 0xffff007fc1ffcff3

def z284 : W := mkw 0x0000000000000000 0x0000000000000000 0x6000000080010843 0x1800000020004210

def z285 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000100898000003 0x9000040226000000

def z286 : W := mkw 0x0021100000046000 0x0008440000011800 0xec731180e01ffe73 0xbb1cc4603807ff9c

def z287 : W := mkw 0x049001dd01220f82 0x01240077404883e0 0xf78001ff07e00f82 0x7de0007fc1f803e0

def z288 : W := mkw 0x0b6ffe228eddf000 0x02dbff88a3b77c00 0xfffffe7f9ffff003 0xffffff9fe7fffc00

def z289 : W := mkw 0x0b6b980000cce000 0x02dae60000333800 0xdffffe0000eec001 0xf7ffff80003bb000

def z290 : W := mkw 0x0000000000000000 0x0000000000000000 0x400c007f00000002 0xd003001fc0000000

def z291 : W := mkw 0x0182815041608c20 0x8060a05410582308 0xf78301f067e0ce32 0x7de0c07c19f8338c

def z292 : W := mkw 0x93fbffeefa011045 0x24fefffbbe804411 0xdbfffffff801304f 0xf6fffffffe004c13

def z293 : W := mkw 0x800466338f1118c5 0x2001198ce3c44631 0x000cfe779f01304d 0x40033f9de7c04c13

def z294 : W := mkw 0x0004001105100880 0x0001000441440220 0x000c007707000000 0x4003001dc1c00000

def z295 : W := mkw 0x9127fe33ff1118c5 0x2449ff8cffc44631 0x600ffe7fff1139cf 0xd803ff9fffc44e73

def z296 : W := mkw 0x800066228a011045 0x20001988a2804411 0x6000fe08981139cf 0x98003f8226044e73

def z297 : W := mkw 0x0004001105100880 0x0001000441440220 0x600c007f07100982 0xd803001fc1c40260

def z298 : W := mkw 0x037b988830066318 0x40dee6220c0198c6 0xffffff88f81fffff 0xffffffe23e07ffff

def z299 : W := mkw 0x8186e371c7719ce5 0xa061b8dc71dc6739 0xf783e1f0e7f1ffff 0x7de0f87c39fc7fff

def z300 : W := mkw 0x034ea00006d98000 0x00d3a80001b66000 0xffffe00007ffc001 0xfffff80001fff000

def z301 : W := mkw 0x8b6fba1107ddf8c5 0x22dbee8441f77e31 0xfffffe0007fff9cd 0xffffff8001fffe73

def z302 : W := mkw 0x0beffb70c7fdfc61 0x82fbfedc31ff7f18 0xfffffe7007fff001 0xffffff9c01fffc00

def z303 : W := mkw 0x0000040208000000 0x0000010082000000 0x000c1e0f18000000 0x80030783c6000000

def z304 : W := mkw 0x0927ba0006ddf000 0x0249ee8001b77c00 0x2403fe0007fff001 0x0900ff8001fffc00

def z305 : W := mkw 0x82dc67ff8f1118c5 0x20b719ffe3c44631 0xfbfcffff9f1139cf 0xfeff3fffe7c44e73

def z306 : W := mkw 0x02f911cc30000000 0x00be44730c000000 0xdbff11fff8000003 0xf6ffc47ffe000000

def z307 : W := mkw 0x0000000000066318 0x40000000000198c6 0x04000000000ec630 0x010000000003b18c

def z308 : W := mkw 0x0010008830020318 0x400400220c0080c6 0xec700188f81e0ffe 0xbb1c00623e0783ff

def z309 : W := mkw 0x13ebdd66c8000000 0x04faf759b2000000 0xdbfffe7700000001 0xf6ffff9dc0000000

def z310 : W := mkw 0x800446238c101084 0x20011188e3040421 0x400cfe7f9810318f 0xd0033f9fe6040c63

def z311 : W := mkw 0x8b6ffe228eddf045 0x22dbff88a3b77c11 0xfffffe009ffff04d 0xffffff8027fffc13

def z312 : W := mkw 0x0b6fba0006ddf000 0x02dbee8001b77c00 0x1bfcfe0007fe3000 0xc6ff3f8001ff8c00

def z313 : W := mkw 0x0fffbbdd37ffff9a 0x43ffeef74dffffe6 0xffffffffffffffff 0xffffffffffffffff

def z314 : W := mkw 0x0414009905ba0f82 0x01050026416e83e0 0xec70018807fe0f82 0xbb1c006201ff83e0

def z315 : W := mkw 0x13fb99cc70608420 0x84fee6731c182108 0x9ff3018060e0c630 0x27fcc0601838318c

def z316 : W := mkw 0x13fbd9ecf0000000 0x04fef67b3c000000 0xdbf3e1f0e0000003 0x76fcf87c38000000

def z317 : W := mkw 0x036f980004980000 0x00dbe60001260000 0xfffffe0007fe0001 0xffffff8001ff8000

def z318 : W := mkw 0x0021100000000000 0x0008440000000000 0xc873100000000001 0xb21cc40000000000

def z319 : W := mkw 0x0b6ffa20c6ddf061 0x82dbfe8831b77c18 0xfffffe00e7fff071 0xffffff8039fffc1c

def z320 : W := mkw 0x0182c160c0000000 0x0060b05830000000 0xd383e1f0e0000003 0x74e0f87c38000000

def z321 : W := mkw 0x0000201003618c61 0x8000080400d86318 0x0000000007e00000 0x0000000001f80000

def z322 : W := mkw 0x02d801cc00000000 0x00b6007300000000 0x9bf0018000000000 0x26fc006000000000

def z323 : W := mkw 0x0102a01003618c61 0x8040a80400d86318 0xf783e00007e1ce71 0x7de0f80001f8739c

def z324 : W := mkw 0x8182e573cb618ce5 0xa060b95cf2d86339 0xf783e1ffffe1cfff 0x7de0f87ffff873ff

def z325 : W := mkw 0x0192e1f8c3638f61 0x8064b87e30d8e3d8 0xfff3e1f8e7ffcff3 0xfffcf87e39fff3fc

def z326 : W := mkw 0x0021100000046000 0x0008440000011800 0x8c730000000ec000 0x231cc0000003b000

def z327 : W := mkw 0x0004220006111000 0x0001088001844400 0x2000000007113000 0x0800000001c44c00

def z328 : W := mkw 0x0004623087111841 0x0001188c21c44610 0x600cfe7087113843 0xd8033f9c21c44e10

def z329 : W := mkw 0x800066228a011045 0x20001988a2804411 0x400cfe7f9801304f 0xd0033f9fe6004c13

def z330 : W := mkw 0x8035329937177bdd 0x600d4ca64dc5def7 0xec731188ff1fffff 0xbb1cc4623fc7ffff

def z331 : W := mkw 0x0b7fba8836dff318 0x42dfeea20db7fcc6 0xfffffe081ffff18d 0xffffff8207fffc63

def z332 : W := mkw 0x01a3f170f365ec79 0xc068fc5c3cd97b1e 0xf783f1f0ffe1fe7f 0x7de0fc7c3ff87f9f

def z333 : W := mkw 0x8004020104101084 0x2001008041040421 0x000000000010318c 0x0000000000040c63

def z334 : W := mkw 0x01a3f170c365ec61 0x8068fc5c30d97b18 0xfff3f1f0e7fffe73 0xfffcfc7c39ffff9c

def z335 : W := mkw 0x93fbddfff90008c5 0x24fef77ffe400231 0xdbfffffff80009cf 0xf6fffffffe000273

def z336 : W := mkw 0x06dc41fdc5ba0fe3 0x81b7107f716e83f8 0xfffc01ffe7fe0ff2 0xffff007ff9ff83fc

def z337 : W := mkw 0x0000403081000841 0x0000100c20400210 0x0000007080000842 0x0000001c20000210

def z338 : W := mkw 0x0182e170c3618c61 0x8060b85c30d86318 0xd383e1f0e7e00003 0x74e0f87c39f80000

def z339 : W := mkw 0x1102cc22c8000000 0x0440b308b2000000 0x0000ee0000000000 0x00003b8000000000

def z340 : W := mkw 0x8035168b3c16739c 0x600d45a2cf059ce7 0x087c1e0f181e318c 0x821f0783c6078c63

def z341 : W := mkw 0x12f95deef8000000 0x04be577bbe000000 0x087c1ffff8000002 0x821f07fffe000000

def z342 : W := mkw 0x0182e170c3618c61 0x8060b85c30d86318 0xf783f1f8fff1ffff 0xfde0fc7e3ffc7fff

def z343 : W := mkw 0x06dc01dd05ba0f82 0x01b70077416e83e0 0x087c01ff001e0f82 0x821f007fc00783e0

def z344 : W := mkw 0x0b6fba1007fdfc61 0x82dbee8401ff7f18 0xfffffe0007fffe71 0xffffff8001ffff9c

def z345 : W := mkw 0x17fbddeef8aa0702 0x05fef77bbe2a81c0 0xdffffffff8ee0603 0xf7fffffffe3b8180

def z346 : W := mkw 0x00804170c1200c61 0x8020105c30480318 0x0000007000000000 0x0000001c00000000

def z347 : W := mkw 0x0080015001200c00 0x0020005400480300 0xf78301f0e7e1ce73 0x7de0c07c39f8739c

def z348 : W := mkw 0x1b6ffe22feddf000 0x06dbff88bfb77c00 0xfffffe00fffff001 0xffffff803ffffc00

def z349 : W := mkw 0x0004220006111000 0x0001088001844400 0x000cee0007000000 0x40033b8001c00000

def z350 : W := mkw 0x06dc61fd87bb0fc3 0x01b7187f61eec3f0 0xfffce1ff87ff0fc3 0xffff387fe1ffc3f0

def z351 : W := mkw 0x065c009d059a0b82 0x01970027416682e0 0x687c007f071e0982 0xda1f001fc1c78260

def z352 : W := mkw 0x049401dd05ba0f82 0x01250077416e83e0 0x240001ff07fe0f82 0x0900007fc1ff83e0

def z353 : W := mkw 0x0182e170c3010841 0x0060b85c30c04210 0xf383e1f0e7010843 0x7ce0f87c39c04210

def z354 : W := mkw 0x801466bb8f131bc5 0x200519aee3c4c6f1 0xec7cffff9f1f3fcf 0xfb1f3fffe7c7cff3

def z355 : W := mkw 0x8186e773cf719ce5 0xa061b9dcf3dc6739 0xf78feff7e7e1ce73 0x7de3fbfdf9f8739c

def z356 : W := mkw 0x80217622ba05705d 0x60085d88ae815c17 0x0003fe00f801f07d 0x0000ff803e007c1f

def z357 : W := mkw 0x0fceab5507f99c82 0x03f3aad541fe6720 0x138cee7707e00000 0x44e33b9dc1f80000

def z358 : W := mkw 0x0927ba000655f000 0x0249ee8001957c00 0x600ffe000711f001 0xd803ff8001c47c00

def z359 : W := mkw 0x0edc23dd07ffff82 0x03b708f741ffffe0 0xfffc01ff07ffff82 0xffff007fc1ffffe0

def z360 : W := mkw 0x0b7b988830cee318 0x42dee6220c33b8c6 0xfff31188f8ffffff 0xbffcc4623e3fffff

def z361 : W := mkw 0x800406030c101084 0x20010180c3040421 0x000c0e0700000000 0x00030381c0000000

def z362 : W := mkw 0x07de81dd45fa8fa2 0x81f7a077517ea3e8 0xffff01ff67fecfb2 0xffffc07fd9ffb3ec

def z363 : W := mkw 0x17fb99cc70aa0702 0x05fee6731c2a81c0 0x9ff3018060ee0600 0x27fcc060183b8180

def z364 : W := mkw 0x0010008800020300 0x00040022000080c0 0x0000018800000f82 0x00000062000003e0

def z365 : W := mkw 0x8000060208001004 0x2000018082000401 0x00001e001800300c 0x0000078006000c03

def z366 : W := mkw 0x167d1c8f3c9a0382 0x059f4723cf2680e0 0x087c1e0f181e0180 0x821f0783c6078060

def z367 : W := mkw 0x13fb99cc70066318 0x44fee6731c0198c6 0xfff31188f81fffff 0xbffcc4623e07ffff

def z368 : W := mkw 0x1bceef66ced99000 0x06f3bbd9b3b66400 0x138cee7707e00000 0x44e33b9dc1f80000

def z369 : W := mkw 0x0480015501200c82 0x0120005540480320 0x0000007700000000 0x0000001dc0000000

def z370 : W := mkw 0x0fdeabdd07fb9f82 0x03f7aaf741fee7e0 0xfffcefff07fe0f82 0xffff3bffc1ff83e0

def z371 : W := mkw 0x13ca894440000000 0x04f2a25110000000 0x1380000000000000 0x04e0000000000000

def z372 : W := mkw 0x06dc01cd04ba0782 0x01b70073412e81e0 0x9ffc018f00fe0780 0xa7ff0063c03f81e0

def z373 : W := mkw 0x07dee1fdc7fb8fe3 0x81f7b87f71fee3f8 0xfffce1ff07fe0f82 0xffff387fc1ff83e0

def z374 : W := mkw 0x13fbddfef9200c00 0x04fef77fbe480300 0xffffffffffe00e03 0xfffffffffff80380

def z375 : W := mkw 0x07dea1dd07fb8f82 0x01f7a87741fee3e0 0xffffe1ff07ffcf83 0xfffff87fc1fff3e0

def z376 : W := mkw 0x065c008d049a0382 0x01970023412680e0 0xfffc000f07fe0180 0xffff0003c1ff8060

def z377 : W := mkw 0x17ffddfffdbe6f9a 0x45fff77fff6f9be6 0xffffffffffffffff 0xffffffffffffffff

def z378 : W := mkw 0x0031108830066318 0x400c44220c0198c6 0xec730188601ecfb2 0xbb1cc0621807b3ec

def z379 : W := mkw 0x9bffffffffddf8c5 0x26fffffffff77e31 0xfffffffffffff9cf 0xfffffffffffffe73

def z380 : W := mkw 0x13fb99cc70000000 0x04fee6731c000000 0xdbffff8060000001 0xf6ffffe018000000

def z381 : W := mkw 0x93ceef77cf1118c5 0x24f3bbddf3c44631 0x138cee7707000000 0x44e33b9dc1c00000

def z382 : W := mkw 0x81b7f7fbff77fffd 0xe06dfdfeffddffff 0xffffffffffffffff 0xffffffffffffffff

def z383 : W := mkw 0x0102a00002418000 0x0040a80000906000 0xf783e180e7e1ce73 0x7de0f86039f8739c

def z384 : W := mkw 0x93ffffffff1118c5 0x24ffffffffc44631 0xdbffffffff000003 0xf6ffffffffc00000

def z385 : W := mkw 0x0b6fba0006ddf000 0x02dbee8001b77c00 0xbff3000007fff000 0x2ffcc00001fffc00

def z386 : W := mkw 0x0021100000046000 0x0008440000011800 0x08701000001e3000 0x821c040000078c00

def z387 : W := mkw 0x03dac1ecc0000000 0x00f6b07b30000000 0xdbffe1ffe0000003 0xf6fff87ff8000000

def z388 : W := mkw 0x8923fe228a45f045 0x2248ff88a2917c11 0x0003fe009801f04d 0x0000ff8026007c13

def z389 : W := mkw 0x1bffbbcc76ddf000 0x06ffeef31db77c00 0xffffff8067fff001 0xffffffe019fffc00

def z390 : W := mkw 0x0010008830000000 0x000400220c000000 0x00000188f8000002 0x000000623e000000

def z391 : W := mkw 0x06fd11dd35ba0f82 0x01bf44774d6e83e0 0xffff11fffffe0f83 0xffffc47fffff83e0

def z392 : W := mkw 0x06cc015505b80c82 0x01b30055416e0320 0x738c007f07f00982 0xdce3001fc1fc0260

def z393 : W := mkw 0x0000200002010000 0x0000080000804000 0x6000e00007010001 0x5800380001c04000

def z394 : W := mkw 0x0182c170c1200c61 0x8060b05c30480318 0xd383e1f0e0000e73 0x74e0f87c3800039c

def z395 : W := mkw 0x13fbddeef8000000 0x04fef77bbe000000 0x9bf301fff8000002 0x26fcc07ffe000000

def z396 : W := mkw 0x927d7ebfbf1118c5 0x249f5fafefc44631 0x687cfe7f9f1139cf 0xda1f3f9fe7c44e73

def z397 : W := mkw 0x12d845eef8000000 0x04b6117bbe000000 0xdbfc01fff8000002 0xf6ff007ffe000000

def z398 : W := mkw 0x0010008830020318 0x400400220c0080c6 0x0000018060000630 0x000000601800018c

def z399 : W := mkw 0x17cecd77cdb80c82 0x05f3b35df36e0320 0x138cee7707e00000 0x44e33b9dc1f80000

def z400 : W := mkw 0x0410008d00020382 0x01040023400080e0 0x0000000f00000180 0x00000003c0000060

def z401 : W := mkw 0x0106a20006519000 0x0041a88001946400 0xf78ffe0007f1f001 0xfde3ff8001fc7c00

def z402 : W := mkw 0x1bffffeefed99000 0x06fffffbbfb66400 0xdbffffffffe00003 0xf6fffffffff80000

def z403 : W := mkw 0x0b6f9a0004dcf000 0x02dbe68001373c00 0x9fff1e0000fef000 0xa7ffc780003fbc00

def z404 : W := mkw 0x909045fff90008c5 0x2424117ffe400231 0x000001fff80009ce 0x0000007ffe000273

def z405 : W := mkw 0x17decdffcdba0f82 0x05f7b37ff36e83e0 0xfffcefff07fe0f82 0xffff3bffc1ff83e0

def z406 : W := mkw 0x0031108830066318 0x400c44220c0198c6 0xec701188181e3f8e 0xbb1c046206078fe3

def z407 : W := mkw 0x803154bbb9066bdd 0x600c552eee419af7 0xec7311fff81fffff 0xbb1cc47ffe07ffff

def z408 : W := mkw 0x13fbfdfefb67ef79 0xc4feff7fbed9fbde 0xffffffffffffffff 0xffffffffffffffff

def z409 : W := mkw 0x13fbddeef8020300 0x04fef77bbe0080c0 0xfffffffff81e0f83 0xfffffffffe0783e0

def z410 : W := mkw 0x0000001001200c00 0x0000000400480300 0x2400000007e00e00 0x0900000001f80380

def z411 : W := mkw 0x0000200002418000 0x0000080000906000 0x2400000007e1c000 0x0900000001f87000

def z412 : W := mkw 0x0010008800020300 0x00040022000080c0 0xec730188e01fcff3 0xbb1cc0623807f3fc

def z413 : W := mkw 0x01b391c87066e738 0xc06ce4721c19b9ce 0xfff31188f8ffffff 0xbffcc4623e3fffff

def z414 : W := mkw 0x0031108830000000 0x000c44220c000000 0x8873018060000000 0x221cc06018000000

def z415 : W := mkw 0x0b7fba8836ddf000 0x02dfeea20db77c00 0xffffff88fffff003 0xffffffe23ffffc00

def z416 : W := mkw 0x06dc01dd05b80c82 0x01b70077416e0320 0xdbfc01ff07e00002 0xf6ff007fc1f80000

def z417 : W := mkw 0x1bfb99cc70cce000 0x06fee6731c333800 0x9ff3018060eec000 0x27fcc060183bb000

def z418 : W := mkw 0x0000201003618c61 0x8000080400d86318 0xe4030180e7e1ce73 0x3900c06039f8739c

def z419 : W := mkw 0x0b6fba0006ddf000 0x02dbee8001b77c00 0xfffffe089ffff9cf 0xffffff8227fffe73

def z420 : W := mkw 0x16fd1ddf3dba0f82 0x05bf4777cf6e83e0 0xfffc1fff1ffe0f82 0xffff07ffc7ff83e0

def z421 : W := mkw 0x07dae1fcc3eb8f63 0x81f6b87f30fae3d8 0xfff3e1f0e7efce73 0x7ffcf87c39fbf39c

def z422 : W := mkw 0x06dc01dd05ba0f82 0x01b70077416e83e0 0xbff0018007fe0f80 0x2ffc006001ff83e0

def z423 : W := mkw 0x0000000000000000 0x0000000000000000 0xf780000007e00000 0x7de0000001f80000

def z424 : W := mkw 0x024c000004980000 0x0093000001260000 0x138c000007e00000 0x44e3000001f80000

def z425 : W := mkw 0x800446338d1018c5 0x2001118ce3440631 0x000c1e7f981039ce 0x8003079fe6040e73

def z426 : W := mkw 0x0484015105ba0f82 0x01210054416e83e0 0xf78001f007fe0f82 0x7de0007c01ff83e0

def z427 : W := mkw 0x0b6ffa3087ddf841 0x02dbfe8c21f77e10 0xfffffe7087fff843 0xffffff9c21fffe10

def z428 : W := mkw 0x109001cc70000000 0x042400731c000000 0x0000018060000000 0x0000006018000000

def z429 : W := mkw 0x801044bbb9020bdd 0x6004112eee4082f7 0x000001fff8000ffe 0x0000007ffe0003ff

def z430 : W := mkw 0x0435109935be6f9a 0x410d44264d6f9be6 0xec731188ffffffff 0xbb1cc4623fffffff

def z431 : W := mkw 0x17ffddfffdb80c82 0x05fff77fff6e0320 0xdbffffffffe00003 0xf6fffffffff80000

def z432 : W := mkw 0x049001dd01220f82 0x01240077404883e0 0xec7001ff001e0f82 0xbb1c007fc00783e0

def z433 : W := mkw 0x0000200002418061 0x8000080000906018 0x000000000001c070 0x000000000000701c

def z434 : W := mkw 0x0000001001200c61 0x8000000400480318 0x0000000000000e70 0x000000000000039c

def z435 : W := mkw 0x800466338f719ce5 0xa001198ce3dc6739 0x640cfe7f9ff1ffff 0xd9033f9fe7fc7fff

def z436 : W := mkw 0x0902aa0002419000 0x0240aa8000906400 0x0000ee0000000000 0x00003b8000000000

def z437 : W := mkw 0x0021100030046018 0x400844000c011806 0xe4031180f801fe7f 0x3900c4603e007f9f

def z438 : W := mkw 0x0a7d1a88349e7318 0x429f46a20d279cc6 0xec7f1f88f81fffff 0xbb1fc7e23e07ffff

def z439 : W := mkw 0x8404221107bb1fc7 0x2101088441eec7f1 0x2400000007ff3fcc 0x0900000001ffcff3

def z440 : W := mkw 0x0b4eaa0006ddf000 0x02d3aa8001b77c00 0x378cee0007fff000 0x4de33b8001fffc00

def z441 : W := mkw 0x13fbddfef9200c61 0x84fef77fbe480318 0xdbfffffff8000e73 0xf6fffffffe00039c

def z442 : W := mkw 0x0010008800020300 0x00040022000080c0 0xec701188981f3fcf 0xbb1c04622607cff3

def z443 : W := mkw 0x037b988830000000 0x00dee6220c000000 0xdbffff88f8000003 0xf6ffffe23e000000

def z444 : W := mkw 0x8004221107177bdd 0x6001088441c5def7 0x24000000071ffffc 0x0900000001c7ffff

def z445 : W := mkw 0x0e7d1a8d049e7382 0x039f46a341279ce0 0x087c1e0f001e3180 0x821f0783c0078c60

def z446 : W := mkw 0x800466338f1118c5 0x2001198ce3c44631 0x2000fe009f1139cd 0x08003f8027c44e73

def z447 : W := mkw 0x0031108830066318 0x400c44220c0198c6 0x8c731180f80ff67d 0x231cc4603e03fd9f

def z448 : W := mkw 0x800406030c101084 0x20010180c3040421 0x600c1e0f981139cf 0x98030783e6044e73

def z449 : W := mkw 0x109045eef8020318 0x4424117bbe0080c6 0x000001fff8000ffe 0x0000007ffe0003ff

def z450 : W := mkw 0x0133f0a8f247e379 0xc04cfc2a3c91f8de 0xec73f188f81fffff 0xbb1cfc623e07ffff

def z451 : W := mkw 0x1010048e38000000 0x040401238e000000 0x0000000f18000000 0x00000003c6000000

def z452 : W := mkw 0x13caed76cb618c61 0x84f2bb5db2d86318 0xf78feff7e7e1ce73 0x7de3fbfdf9f8739c

def z453 : W := mkw 0x0000000000000000 0x0000000000000000 0x400cfe0000000001 0xd0033f8000000000

def z454 : W := mkw 0x0182814040608420 0x8060a05010182108 0x1380000000e00000 0x04e0000000380000

def z455 : W := mkw 0x13fb9dce78000000 0x04fee7739e000000 0x9bff1f8f78000000 0xa6ffc7e3de000000

def z456 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0030180e0000003 0x3000c06038000000

def z457 : W := mkw 0x1fffffffffffff82 0x07ffffffffffffe0 0xffffffffffffff83 0xffffffffffffffe0

def z458 : W := mkw 0x06d801dd01220f82 0x01b60077404883e0 0xdbfc01ff00000f82 0xf6ff007fc00003e0

def z459 : W := mkw 0x800466338f1118c5 0x2001198ce3c44631 0x600cfe7707113001 0xd8033f9dc1c44c00

def z460 : W := mkw 0x02cc015005b80c00 0x00b30054016e0300 0xfffc01f007fe0e02 0xffff007c01ff8380

def z461 : W := mkw 0x049001cc00220702 0x01240073000881c0 0x0000018000000600 0x0000006000000180

def z462 : W := mkw 0x0000000000000000 0x0000000000000000 0x240000000001ce70 0x090000000000739c

def z463 : W := mkw 0x0186e171c7718ce1 0x8061b85c71dc6338 0xf78fe1ffe7f1cff3 0xfde3f87ff9fc73fc

def z464 : W := mkw 0x067d108d349e639a 0x419f44234d2798e6 0xec7f118ff81fffff 0xbb1fc463fe07ffff

def z465 : W := mkw 0x17ffddeffc9a0382 0x05fff77bff2680e0 0xdbfffffff81e0183 0xf6fffffffe078060

def z466 : W := mkw 0x865c66bf8f9b1bc7 0x219719afe3e6c6f1 0x687cfe7f9f1f39cf 0xda1f3f9fe7c7ce73

def z467 : W := mkw 0x003130983367ef79 0xc00c4c260cd9fbde 0xec731188ffffffff 0xbb1cc4623fffffff

def z468 : W := mkw 0x80046231871118c5 0x2001188c61c44631 0x6000e070871139cf 0x5800381c21c44e73

def z469 : W := mkw 0x03fb99cc00000000 0x00fee67300000000 0xdbffffff00000003 0xf6ffffffc0000000

def z470 : W := mkw 0x02c8014400000000 0x00b2005100000000 0x138c007700000000 0x44e3001dc0000000

def z471 : W := mkw 0x0031108830066318 0x400c44220c0198c6 0xc8731188f81e318f 0xb21cc4623e078c63

def z472 : W := mkw 0x0000603083010841 0x0000180c20c04210 0x6000f0789f1139cf 0xd8003c1e27c44e73

def z473 : W := mkw 0x049001dd31220f9a 0x412400774c4883e6 0x000001fff8000ffe 0x0000007ffe0003ff

def z474 : W := mkw 0x10b155eef8000000 0x042c557bbe000000 0xc87311fff8000003 0xb21cc47ffe000000

def z475 : W := mkw 0x0031108830066318 0x400c44220c0198c6 0x2c701008181ffffc 0x8b1c04020607ffff

def z476 : W := mkw 0x0031108830066318 0x400c44220c0198c6 0x68701008981f39cf 0x9a1c04022607ce73

def z477 : W := mkw 0x16dc45fffdba0f82 0x05b7117fff6e83e0 0xfffc01fffffe0f82 0xffff007fffff83e0

def z478 : W := mkw 0x0000402080000000 0x0000100820000000 0x4000e07080000003 0x5000381c20000000

def z479 : W := mkw 0x0000603083618c61 0x8000180c20d86318 0x6400e07087e1ce73 0x5900381c21f8739c

def z480 : W := mkw 0x86dc45ff8dba0fc7 0x21b7117fe36e83f1 0xfffc01ff9ffe0fce 0xffff007fe7ff83f3

def z481 : W := mkw 0x0025320006157000 0x00094c8001855c00 0xec7ffe00071ff001 0xfb1fff8001c7fc00

def z482 : W := mkw 0x0004000004980000 0x0001000001260000 0x2400000007fe0000 0x0900000001ff8000

def z483 : W := mkw 0x025c0088049a0300 0x00970022012680c0 0xfffc018807fe0f82 0xffff006201ff83e0

def z484 : W := mkw 0x06fd11dd35be6f9a 0x41bf44774d6f9be6 0xffff01ff67fecfb2 0xffffc07fd9ffb3ec

def z485 : W := mkw 0x0102e020c2418061 0x8040b80830906018 0xf783e000e7e1c071 0x7de0f80039f8701c

def z486 : W := mkw 0x80004433890008c5 0x2000110ce2400231 0x0000007700000000 0x0000001dc0000000

def z487 : W := mkw 0x800466338f1118c5 0x2001198ce3c44631 0x200cee77071139cc 0x48033b9dc1c44e73

def z488 : W := mkw 0x800426030e111084 0x20010980c3844421 0x600cfe0f1f11318d 0xd8033f83c7c44c63

def z489 : W := mkw 0x02d801dc01200c00 0x00b6007700480300 0xfffc01ff07e00e02 0xffff007fc1f80380

def z490 : W := mkw 0x0000442288000000 0x00001108a2000000 0x0000fe0098000001 0x00003f8026000000

def z491 : W := mkw 0x13ffddfffd100880 0x04fff77fff440220 0xfbffffffff100983 0xfeffffffffc40260

def z492 : W := mkw 0x803176aaba07735d 0x600c5daaae81dcd7 0xec73ff88f81fffff 0xbb1cffe23e07ffff

def z493 : W := mkw 0x03ebf970c3618c61 0x80fafe5c30d86318 0xfffffff0e7e1ce73 0xfffffffc39f8739c

def z494 : W := mkw 0x0000201003010841 0x0000080400c04210 0x2000000007010840 0x0800000001c04210

def z495 : W := mkw 0x01b3d1e8f0000000 0x006cf47a3c000000 0xdbf3f1f8f8000003 0xf6fcfc7e3e000000

def z496 : W := mkw 0x0021100030046018 0x400844000c011806 0x000300006000c030 0x0000c0001800300c

def z497 : W := mkw 0x01b391c87066e738 0xc06ce4721c19b9ce 0x9ff3018060eec630 0x27fcc060183bb18c

def z498 : W := mkw 0x0010008800020300 0x00040022000080c0 0x08700008001e0180 0x821c000200078060

def z499 : W := mkw 0x0000602082010041 0x0000180820804010 0x0000e00080010041 0x0000380020004010

def z500 : W := mkw 0x86fd77ffbfbf7fdf 0x61bf5dffefefdff7 0xffffffffffffffff 0xffffffffffffffff

def z501 : W := mkw 0x0269180000000000 0x009a460000000000 0x087c1e0000000000 0x821f078000000000

def z502 : W := mkw 0x000064328b010841 0x0000190ca2c04210 0x600cfe7f9f010843 0xd8033f9fe7c04210

def z503 : W := mkw 0x0031108800066300 0x000c4422000198c0 0xec731188001fff83 0xbb1cc4620007ffe0

def z504 : W := mkw 0x000466228e111000 0x00011988a3844400 0x600cfe7f9f113003 0xd8033f9fe7c44c00

def z505 : W := mkw 0x0123f020f245e079 0xc048fc083c91781e 0x0003f000f801f07d 0x0000fc003e007c1f

def z506 : W := mkw 0x06dc23dd07bb1f82 0x01b708f741eec7e0 0xfffcffff07ff3f83 0xffff3fffc1ffcfe0

def z507 : W := mkw 0x0004001105100880 0x0001000441440220 0x600c107f9f1139cf 0xd803041fe7c44e73

def z508 : W := mkw 0x13fbfdfefb010841 0x04feff7fbec04210 0xfbffffffff010843 0xfeffffffffc04210

def z509 : W := mkw 0x02dc01cc04980000 0x00b7007301260000 0xfffc01ff07fe0002 0xffff007fc1ff8000

def z510 : W := mkw 0x0000442288000000 0x00001108a2000000 0x0000007f98000002 0x0000001fe6000000

def z511 : W := mkw 0x0a4c0a0004981000 0x0293028001260400 0x000c0e0000000000 0x0003038000000000

def z512 : W := mkw 0x0b7fba8806dff300 0x02dfeea201b7fcc0 0xffffff8807ffff83 0xffffffe201ffffe0

def z513 : W := mkw 0x800466338f1118c5 0x2001198ce3c44631 0x000cee7f9f0009ce 0x40033b9fe7c00273

def z514 : W := mkw 0x036bdc2288000000 0x00daf708a2000000 0xdbfffe7f98000003 0xf6ffff9fe6000000

def z515 : W := mkw 0x0986e370c7fdfc61 0x8261b8dc31ff7f18 0xf783e1f0e7fffe73 0x7de0f87c39ffff9c

def z516 : W := mkw 0x80042211071118c5 0x2001088441c44631 0x600cfe00071139cd 0xd8033f8001c44e73

def z517 : W := mkw 0x0000000000000000 0x0000000000000000 0xec700000001e0000 0xbb1c000000078000

def z518 : W := mkw 0x0933ba883247f318 0x424ceea20c91fcc6 0xec73ff88f81fffff 0xbb1cffe23e07ffff

def z519 : W := mkw 0x0000000000066318 0x40000000000198c6 0x64001008981fffff 0x990004022607ffff

def z520 : W := mkw 0x0021100030046018 0x400844000c011806 0x000010001800300c 0x0000040006000c03

def z521 : W := mkw 0x00b151f8f1266f79 0xc02c547e3c499bde 0xec7311f8f81fffff 0xbb1cc47e3e07ffff

def z522 : W := mkw 0x0586e171c7fb8fe3 0x8161b85c71fee3f8 0xf783e1f0e7ffcff3 0x7de0f87c39fff3fc

def z523 : W := mkw 0x0031108830046000 0x000c44220c011800 0xec731188f81ff003 0xbb1cc4623e07fc00

def z524 : W := mkw 0x10211c0238000000 0x040847008e000000 0x00001e0018000000 0x0000078006000000

def z525 : W := mkw 0x8000040308000084 0x20000100c2000021 0x0000000f1800018c 0x00000003c6000063

def z526 : W := mkw 0x80257633bf1578dd 0x60095d8cefc55e37 0x600ffe7fff11f9ff 0xd803ff9fffc47e7f

def z527 : W := mkw 0x0b6b980000cce000 0x02dae60000333800 0xfff3100000fff001 0xbffcc400003ffc00

def z528 : W := mkw 0x0080014040200420 0x8020005010080108 0x0000018060000630 0x000000601800018c

def z529 : W := mkw 0x04040001049a0382 0x01010000412680e0 0x00000000001e0180 0x0000000000078060

def z530 : W := mkw 0x800066338b0118c5 0x2000198ce2c04631 0x0000fe7f980139cf 0x00003f9fe6004e73

def z531 : W := mkw 0x0fffbbcc06fff702 0x03ffeef301bffdc0 0xffffff8007fff601 0xffffffe001fffd80

def z532 : W := mkw 0x0ffb99cc00eee702 0x03fee673003bb9c0 0x9ff3018000eec600 0x27fcc060003bb180

def z533 : W := mkw 0x80004433890008c5 0x2000110ce2400231 0x400cfe7f980009cf 0xd0033f9fe6000273

def z534 : W := mkw 0x0031108830066318 0x400c44220c0198c6 0xec731180601ff631 0xbb1cc4601807fd8c

def z535 : W := mkw 0x0021100030000000 0x000844000c000000 0x00031000f8000001 0x0000c4003e000000

def z536 : W := mkw 0x080022000245f000 0x0200088000917c00 0x000000000001f000 0x0000000000007c00

def z537 : W := mkw 0x0404001105ba0f82 0x01010004416e83e0 0x640c007f07fe0f82 0xd903001fc1ff83e0

def z538 : W := mkw 0x8a6d1e030c9c7084 0x229b4780c3271c21 0x087c1e0f181e318c 0x821f0783c6078c63

def z539 : W := mkw 0x149045fff9220f82 0x0524117ffe4883e0 0x000001fff8000f82 0x0000007ffe0003e0

def z540 : W := mkw 0x07ff99dd05ba0f82 0x01ffe677416e83e0 0xffffffff07fe0f83 0xffffffffc1ff83e0

def z541 : W := mkw 0x0000000000020300 0x00000000000080c0 0x24000000001e0f80 0x09000000000783e0

def z542 : W := mkw 0x0010008830020318 0x400400220c0080c6 0xe4030188f801cfff 0x3900c0623e0073ff

def z543 : W := mkw 0x0031108830046018 0x400c44220c011806 0xc8731188f801f07f 0xb21cc4623e007c1f

def z544 : W := mkw 0x1123980070000000 0x0448e6001c000000 0x0003000060000000 0x0000c00018000000

def z545 : W := mkw 0x80000011010008c5 0x2000000440400231 0x00000000000009cc 0x0000000000000273

def z546 : W := mkw 0x8186e773cf719ce5 0xa061b9dcf3dc6739 0x738cfe7f9ff139cf 0xdce33f9fe7fc4e73

def z547 : W := mkw 0x0102a00002418000 0x0040a80000906000 0x0003e0000001c001 0x0000f80000007000

def z548 : W := mkw 0x0102800040408020 0x8040a00010102008 0x000300006000c030 0x0000c0001800300c

def z549 : W := mkw 0x0923ba000245f000 0x0248ee8000917c00 0xf783fe0007e1f001 0x7de0ff8001f87c00

def z550 : W := mkw 0x06d801dc01aa0f02 0x01b60077006a83c0 0xfff001f007ee0e02 0x7ffc007c01fb8380

def z551 : W := mkw 0x800444338d1008c5 0x2001110ce3440231 0x600c007f9f1009ce 0xd803001fe7c40273

def z552 : W := mkw 0x0004220006111000 0x0001088001844400 0x600cfe089f1139cf 0xd8033f8227c44e73

def z553 : W := mkw 0x0b7b988830cee318 0x42dee6220c33b8c6 0x9ff3018060eec630 0x27fcc060183bb18c

def z554 : W := mkw 0x0592e1fdc3638fe3 0x8164b87f70d8e3f8 0xf783e1ffe7e1cff3 0x7de0f87ff9f873fc

def z555 : W := mkw 0x0800000000cce000 0x0200000000333800 0x0400000000eec000 0x01000000003bb000

def z556 : W := mkw 0x0182e160c2418061 0x8060b85830906018 0xd383e1f0e001c073 0x74e0f87c3800701c

def z557 : W := mkw 0x024c000004980000 0x0093000001260000 0x087c0000001e0000 0x821f000000078000

def z558 : W := mkw 0x137b9c8e38000000 0x04dee7238e000000 0xdbfffe0f18000001 0xf6ffff83c6000000

def z559 : W := mkw 0x0010008800066318 0x40040022000198c6 0xec700188001ffffe 0xbb1c00620007ffff

def z560 : W := mkw 0x8182e772cb619c65 0xa060b9dcb2d86719 0xf783fff0ffe1fe7f 0x7de0fffc3ff87f9f

def z561 : W := mkw 0x12791c8e38000000 0x049e47238e000000 0xc87f1f8ff8000003 0xb21fc7e3fe000000

def z562 : W := mkw 0x0a7d1a88349e7318 0x429f46a20d279cc6 0x087c1e08181e318c 0x821f078206078c63

def z563 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000008980009ce 0x0000000226000273

def z564 : W := mkw 0x13caed76cb618c61 0x84f2bb5db2d86318 0x138cee7707e00000 0x44e33b9dc1f80000

def z565 : W := mkw 0x06fd11dd35be6f9a 0x41bf44774d6f9be6 0xfffc11ff1ffe3f8e 0xffff047fc7ff8fe3

def z566 : W := mkw 0x0404201107fb8fe3 0x8101080441fee3f8 0x2400000007ffcff0 0x0900000001fff3fc

def z567 : W := mkw 0x80004433890008c5 0x2000110ce2400231 0x6000107f981139cf 0x9800041fe6044e73

def z568 : W := mkw 0x00804160c0000000 0x0020105830000000 0x000001f0e0000002 0x0000007c38000000

def z569 : W := mkw 0x8102e622ca419065 0xa040b988b2906419 0x0003fe00f801f07d 0x0000ff803e007c1f

def z570 : W := mkw 0x0000000000020318 0x40000000000080c6 0x0000000000000ffc 0x00000000000003ff

def z571 : W := mkw 0x8b4eee338fd998c5 0x22d3bb8ce3f66631 0x738cfe7f9ff139cf 0xdce33f9fe7fc4e73

def z572 : W := mkw 0x00806170c3618c61 0x8020185c30d86318 0x240001f0e7e1ce72 0x0900007c39f8739c

def z573 : W := mkw 0x8befff73cffdfce5 0xa2fbffdcf3ff7f39 0xffffffffffffffff 0xffffffffffffffff

def z574 : W := mkw 0x0031108830066318 0x400c44220c0198c6 0x00031188f801ffff 0x0000c4623e007fff

def z575 : W := mkw 0x009041f8f1220f79 0xc024107e3c4883de 0x000001f8f8000ffe 0x0000007e3e0003ff

def z576 : W := mkw 0x1a7d1e8e3c9c7000 0x069f47a38f271c00 0x087c1e0f181e3000 0x821f0783c6078c00

def z577 : W := mkw 0x0b6fba0006dff318 0x42dbee8001b7fcc6 0xfffffe0007fffffd 0xffffff8001ffffff

def z578 : W := mkw 0x1b7fbe8e3eddf000 0x06dfefa38fb77c00 0xfffffe0f1ffff001 0xffffff83c7fffc00

def z579 : W := mkw 0x03dae1fcc3618c61 0x80f6b87f30d86318 0xffffe1ffe7e1ce73 0xfffff87ff9f8739c

def z580 : W := mkw 0x0182e170c367ef79 0xc060b85c30d9fbde 0xf783e1f0e7ffffff 0x7de0f87c39ffffff

def z581 : W := mkw 0x8b6ffe338fddf8c5 0x22dbff8ce3f77e31 0xfffffe7707fff001 0xffffff9dc1fffc00

def z582 : W := mkw 0x0000001101000880 0x0000000440400220 0x0000007f00000982 0x0000001fc0000260

def z583 : W := mkw 0x8186e773cf719ce5 0xa061b9dcf3dc6739 0x138cee7707e00000 0x44e33b9dc1f80000

def z584 : W := mkw 0x803576bbbf177bdd 0x600d5daeefc5def7 0x687cfe7f9f1f39cf 0xda1f3f9fe7c7ce73

def z585 : W := mkw 0x0000000030000018 0x400000000c000006 0x00000000f800007c 0x000000003e00001f

def z586 : W := mkw 0x034a880000000000 0x00d2a20000000000 0x138cee0000000000 0x44e33b8000000000

def z587 : W := mkw 0x0258008c00000000 0x0096002300000000 0x087c000f00000000 0x821f0003c0000000

def z588 : W := mkw 0x09a3fb70c365fc61 0x8268fedc30d97f18 0xf783fff0e7e1fe73 0x7de0fffc39f87f9c

def z589 : W := mkw 0x0a4c220006ddf000 0x0293088001b77c00 0xfffc000007fff000 0xffff000001fffc00

def z590 : W := mkw 0x0b4eaa0006d99000 0x02d3aa8001b66400 0x738cfe0007f13001 0xdce33f8001fc4c00

def z591 : W := mkw 0x909467ffff1118c5 0x242519ffffc44631 0x600cffffff1139cf 0xd8033fffffc44e73

def z592 : W := mkw 0x80804573c9200ce5 0xa020115cf2480339 0x000001fff8000ffe 0x0000007ffe0003ff

def z593 : W := mkw 0x800426130f1118c5 0x20010984c3c44631 0x200c1e0f1f1139cc 0x88030783c7c44e73

def z594 : W := mkw 0x0010008830020318 0x400400220c0080c6 0x60001188f8113fff 0x980004623e044fff

def z595 : W := mkw 0x0123b0000245e000 0x0048ec0000917800 0xfff3f00007fff001 0xfffcfc0001fffc00

def z596 : W := mkw 0x800466338f177bdd 0x6001198ce3c5def7 0x640cfe7f9f1fffff 0xd9033f9fe7c7ffff

def z597 : W := mkw 0x07dec1fdc5ba0f82 0x01f7b07f716e83e0 0xffffe1ffe7fe0f83 0xfffff87ff9ff83e0

def z598 : W := mkw 0x0b6bba0002cdf000 0x02daee8000b37c00 0x9ff3fe0000eff001 0x27fcff80003bfc00

def z599 : W := mkw 0x0bfffbf8f7ffff79 0xc2fffefe3dffffde 0xfffffff8ffffffff 0xfffffffe3fffffff

def z600 : W := mkw 0x07cee175c7f98ce3 0x81f3b85d71fe6338 0xf78fe1f7e7e1ce73 0x7de3f87df9f8739c

def z601 : W := mkw 0x0182e170c3618c61 0x8060b85c30d86318 0x7380e07087e10843 0x5ce0381c21f84210

def z602 : W := mkw 0x0a6d3a00069d7000 0x029b4e8001a75c00 0x687cfe00071f3001 0xda1f3f8001c7cc00

def z603 : W := mkw 0x0010008830066318 0x400400220c0198c6 0x24000188f81ffffe 0x090000623e07ffff

def z604 : W := mkw 0x0102e020c2418061 0x8040b80830906018 0xe403e180e001ce73 0x3900f8603800739c

def z605 : W := mkw 0x8b4eee338fd998c5 0x22d3bb8ce3f66631 0x138cee7707e00000 0x44e33b9dc1f80000

def z606 : W := mkw 0x0000000000000000 0x0000000000000000 0x840301806000c630 0x2100c0601800318c

def z607 : W := mkw 0x0021100000046000 0x0008440000011800 0x000310000001f001 0x0000c40000007c00

def z608 : W := mkw 0x0031108830000000 0x000c44220c000000 0xe8731188f81139cf 0xba1cc4623e044e73

def z609 : W := mkw 0x0404001105be6f9a 0x41010004416f9be6 0x2400000007fffffc 0x0900000001ffffff

def z610 : W := mkw 0x13fbfdfefb618c61 0x84feff7fbed86318 0xdbffffffffe00003 0xf6fffffffff80000

def z611 : W := mkw 0x026d1000049c6000 0x009b440001271800 0xffff100007fff001 0xffffc40001fffc00

def z612 : W := mkw 0x801466bbbf131bdd 0x600519aeefc4c6f7 0x600cffffff113fff 0xd8033fffffc44fff

def z613 : W := mkw 0x0186e370c7719c61 0x8061b8dc31dc6718 0xf78ffff0e7f1fe73 0xfde3fffc39fc7f9c

def z614 : W := mkw 0x0182814040608420 0x8060a05010182108 0xf7830180e0e1ce73 0x3de0c0603838739c

def z615 : W := mkw 0x0b6fba1107ddf880 0x02dbee8441f77e20 0xfffffe7f07fff983 0xffffff9fc1fffe60

def z616 : W := mkw 0x0b6f980004dce000 0x02dbe60001373800 0xffff000007fec000 0xffffc00001ffb000

def z617 : W := mkw 0x0010008830020318 0x400400220c0080c6 0x000000081800018c 0x0000000206000063

def z618 : W := mkw 0x0031108830066318 0x400c44220c0198c6 0x8c731188781ef7bc 0xa31cc4621e07bdef

def z619 : W := mkw 0x009001cc00000000 0x0024007300000000 0x000001ff00000002 0x0000007fc0000000

def z620 : W := mkw 0x0031108830066318 0x400c44220c0198c6 0xac730180601ffffc 0x2b1cc0601807ffff

def z621 : W := mkw 0x13fbfdeefa418000 0x04feff7bbe906000 0xffffffffffe1c003 0xfffffffffff87000

def z622 : W := mkw 0x0906a20006ddf000 0x0241a88001b77c00 0xf783e00007fff001 0x7de0f80001fffc00

def z623 : W := mkw 0x0c04221107ffff82 0x0301088441ffffe0 0x2400000007ffff80 0x0900000001ffffe0

def z624 : W := mkw 0x06fd11dd05be6f82 0x01bf4477416f9be0 0xffff11ff07ffff83 0xffffc47fc1ffffe0

def z625 : W := mkw 0x17fffdfffffb8fe3 0x85ffff7ffffee3f8 0xffffffffffffcff3 0xfffffffffffff3fc

def z626 : W := mkw 0x836ffe338f1118c5 0x20dbff8ce3c44631 0xfbfffe7f9f1139cf 0xfeffff9fe7c44e73

def z627 : W := mkw 0x800466338f1118c5 0x2001198ce3c44631 0x400cfe7f9f000003 0xd0033f9fe7c00000

def z628 : W := mkw 0x0080014000000000 0x0020005000000000 0xd38001f000000002 0x74e0007c00000000

def z629 : W := mkw 0x13ffddeefc980000 0x04fff77bbf260000 0xfffffffffffe0003 0xffffffffffff8000

def z630 : W := mkw 0x02dc01dd05100880 0x00b7007741440220 0xfbfc01ff07100982 0xfeff007fc1c40260

def z631 : W := mkw 0x0fefbb5507fdfc82 0x03fbeed541ff7f20 0xfffffe7707fff001 0xffffff9dc1fffc00

def z632 : W := mkw 0x1133dcaaf8000000 0x044cf72abe000000 0xc873ff88f8000003 0xb21cffe23e000000

def z633 : W := mkw 0x0014009905120b80 0x00050026414482e0 0xec7c01ff071e0f82 0xfb1f007fc1c783e0

def z634 : W := mkw 0x0031108830066318 0x400c44220c0198c6 0xec730180e00fce73 0x3b1cc0603803f39c

def z635 : W := mkw 0x0080215003618c61 0x8020085400d86318 0xf78001f007e1ce72 0x7de0007c01f8739c

def z636 : W := mkw 0x0bceeb70c7f99c61 0x82f3badc31fe6718 0x138cee7007e00000 0x44e33b9c01f80000

def z637 : W := mkw 0x0123980000000000 0x0048e60000000000 0x0003fe0000000001 0x0000ff8000000000

def z638 : W := mkw 0x0f6fba1107ffff82 0x03dbee8441ffffe0 0xfffffe0007ffff81 0xffffff8001ffffe0

def z639 : W := mkw 0x036b980000000000 0x00dae60000000000 0x9bf3000000000000 0x26fcc00000000000

def z640 : W := mkw 0x0000000000000000 0x0000000000000000 0x6000000800100982 0x9800000200040260

def z641 : W := mkw 0x06dc01cd049a0382 0x01b70073412680e0 0xdbfc01ff001e0182 0xf6ff007fc0078060

def z642 : W := mkw 0x06d801dd01aa0f82 0x01b60077406a83e0 0x9ff001ff00ee0f82 0x27fc007fc03b83e0

def z643 : W := mkw 0x0182e170c3618c61 0x8060b85c30d86318 0x1383e070e7e1c071 0x44e0f81c39f8701c

def z644 : W := mkw 0x0befbb5007fdfc00 0x02fbeed401ff7f00 0xfffffff007fffe03 0xfffffffc01ffff80

def z645 : W := mkw 0x0658008c008a0302 0x01960023002280c0 0x08700000000e0000 0x021c000000038000

def z646 : W := mkw 0x800064338b0108c5 0x2000190ce2c04231 0x6000e07f9f0109cf 0x5800381fe7c04273

def z647 : W := mkw 0x0b6bba000245f000 0x02daee8000917c00 0xdbfffe000001f001 0xf6ffff8000007c00

def z648 : W := mkw 0x800466338f1118c5 0x2001198ce3c44631 0x600cee7787010843 0x58033b9de1c04210

def z649 : W := mkw 0x07fff1fdf7ffeffb 0xc1fffc7f7dfffbfe 0xfffff1ffffffffff 0xfffffc7fffffffff

def z650 : W := mkw 0x800066328b011845 0x2000198ca2c04611 0x6000fe709f01384f 0x58003f9c27c04e13

def z651 : W := mkw 0x8fffffff8fffffc7 0x23ffffffe3fffff1 0xffffffff9fffffcf 0xffffffffe7fffff3

def z652 : W := mkw 0x0102a00002418000 0x0040a80000906000 0x1380e00007e00000 0x44e0380001f80000

def z653 : W := mkw 0x0f7fba8d06dff382 0x03dfeea341b7fce0 0xfffffe0f07fff181 0xffffff83c1fffc60

def z654 : W := mkw 0x800466338f1118c5 0x2001198ce3c44631 0x600cee7f07100982 0xd8033b9fc1c40260

def z655 : W := mkw 0x8106e6338f5198c5 0x2041b98ce3d46631 0xf78ffe7f9ff1f9cf 0xfde3ff9fe7fc7e73

def z656 : W := mkw 0x0102800000408000 0x0040a00000102000 0x9783000000e0c000 0x25e0c00000383000

def z657 : W := mkw 0x0248000000000000 0x0092000000000000 0xdbfc000000000000 0xf6ff000000000000

def z658 : W := mkw 0x04b111dd31266f9a 0x412c44774c499be6 0xec7311fff81fffff 0xbb1cc47ffe07ffff

def z659 : W := mkw 0x0bffbbcc06ddf000 0x02ffeef301b77c00 0xffffffff07fff003 0xffffffffc1fffc00

def z660 : W := mkw 0x0b6bb80002cde000 0x02daee0000b37800 0xfff3e00007efc001 0x7ffcf80001fbf000

def z661 : W := mkw 0x0835328836dff318 0x420d4ca20db7fcc6 0xec731188ffffffff 0xbb1cc4623fffffff

def z662 : W := mkw 0x13fb99cc70000000 0x04fee6731c000000 0xdbf31188f8000003 0xb6fcc4623e000000

def z663 : W := mkw 0x0000000000046018 0x4000000000011806 0x000000000001f07c 0x0000000000007c1f

def z664 : W := mkw 0x11a3dd62f8000000 0x0468f758be000000 0xd383fff0f8000003 0x74e0fffc3e000000

def z665 : W := mkw 0x036fba0006111000 0x00dbee8001844400 0xfbfffe0007113001 0xfeffff8001c44c00

def z666 : W := mkw 0x06dc01dd05be6f9a 0x41b70077416f9be6 0xfffc01ff07fffffe 0xffff007fc1ffffff

def z667 : W := mkw 0x1bffdfeefc9c7000 0x06fff7fbbf271c00 0xdbfffffff81e3003 0xf6fffffffe078c00

def z668 : W := mkw 0x009001d801220f00 0x00240076004883c0 0xfff001f807fe0f82 0xfffc007e01ff83e0

def z669 : W := mkw 0x06cc015505b80c82 0x01b30055416e0320 0xf78c01f707e00e02 0x7de3007dc1f80380

def z670 : W := mkw 0x136bdc22f8000000 0x04daf708be000000 0xdbfffe00f8000001 0xf6ffff803e000000

def z671 : W := mkw 0x0182c170c1200c00 0x0060b05c30480300 0xf783e1f0e7e00e03 0x7de0f87c39f80380

def z672 : W := mkw 0x00806170c3210c61 0x8020185c30c84318 0x6000e1f0e7010e73 0x5800387c39c0439c

def z673 : W := mkw 0x8927fe338f55f8c5 0x2249ff8ce3d57e31 0x600ffe7f9f11f9cf 0xd803ff9fe7c47e73

def z674 : W := mkw 0x0000000000000000 0x0000000000000000 0x00030000e001c071 0x0000c0003800701c

def z675 : W := mkw 0x00804170c1200c61 0x8020105c30480318 0xe40301f0e001ce73 0x3900c07c3800739c

def z676 : W := mkw 0x0804221007fdfc61 0x8201088401ff7f18 0x2400000007fffe70 0x0900000001ffff9c

def z677 : W := mkw 0x0182a15003618c00 0x0060a85400d86300 0xf783e1f007e1ce03 0x7de0f87c01f87380

def z678 : W := mkw 0x0a6d1a00049c7000 0x029b468001271c00 0xec7f1e00001ff001 0xbb1fc7800007fc00

def z679 : W := mkw 0x06c8014400a80402 0x01b20051002a0100 0x1380000000e00000 0x04e0000000380000

def z680 : W := mkw 0x065c009d05ba0f82 0x01970027416e83e0 0x2c7c000f07fe0f80 0x8b1f0003c1ff83e0

def z681 : W := mkw 0x1bfffffefffdfc61 0x86ffffffbfff7f18 0xfffffffffffffe73 0xffffffffffffff9c

def z682 : W := mkw 0x01b3f1f8f3618c61 0x806cfc7e3cd86318 0xfff3f1f8ffe1ce73 0xfffcfc7e3ff8739c

def z683 : W := mkw 0x0021100000046000 0x0008440000011800 0xec731008981ff9cf 0xbb1cc4022607fe73

def z684 : W := mkw 0x800466228e111045 0x20011988a3844411 0x600cfe009f11304d 0xd8033f8027c44c13

def z685 : W := mkw 0x06f911cc30ae671a 0x41be44730c2b99c6 0xfff31188f8ffffff 0xbffcc4623e3fffff

def z686 : W := mkw 0x0031108830066318 0x400c44220c0198c6 0x08731008f81ff1fd 0x821cc4023e07fc7f

def z687 : W := mkw 0x0021100000066318 0x40084400000198c6 0xec731000001ffffd 0xbb1cc4000007ffff

def z688 : W := mkw 0x0b6fba0006d99000 0x02dbee8001b66400 0xdbfffe0007e00001 0xf6ffff8001f80000

def z689 : W := mkw 0x0102c020c0000000 0x0040b00830000000 0x0003e000e0000001 0x0000f80038000000

def z690 : W := mkw 0x86cc67778fb91cc7 0x21b319dde3ee4731 0x138cee7707e00000 0x44e33b9dc1f80000

def z691 : W := mkw 0x01b3f1f8f367ef79 0xc06cfc7e3cd9fbde 0xfff3e1f0e7efce73 0x7ffcf87c39fbf39c

def z692 : W := mkw 0x87dee7ffcffb9fe7 0xa1f7b9fff3fee7f9 0xffffffffffffffff 0xffffffffffffffff

def z693 : W := mkw 0x11b3ddeef8000000 0x046cf77bbe000000 0x0003fffff8000003 0x0000fffffe000000

def z694 : W := mkw 0x0102e030c3618c61 0x8040b80c30d86318 0x2403e000e7e1ce71 0x0900f80039f8739c

def z695 : W := mkw 0x840466338fbb1fc7 0x2101198ce3eec7f1 0x640cfe7f9fff3fcf 0xd9033f9fe7ffcff3

def z696 : W := mkw 0x0102e030c3418861 0x8040b80c30d06218 0x6003e070e701c873 0x5800f81c39c0721c

def z697 : W := mkw 0x0befbb4046fdf420 0x82fbeed011bf7d08 0xffffff8067fff631 0xffffffe019fffd8c

def z698 : W := mkw 0x800466338f1118c5 0x2001198ce3c44631 0x2000007f9f1139ce 0x0800001fe7c44e73

def z699 : W := mkw 0x0000000000000000 0x0000000000000000 0x000010009801304d 0x0000040026004c13

def z700 : W := mkw 0x0b7fba8836dff318 0x42dfeea20db7fcc6 0xffffff8067fff631 0xffffffe019fffd8c

def z701 : W := mkw 0x0beb994040ece420 0x82fae650103b3908 0x9ff3018060eec630 0x27fcc060183bb18c

def z702 : W := mkw 0x03cee170c7f98c61 0x80f3b85c31fe6318 0xffffe1f0e7ffce73 0xfffff87c39fff39c

def z703 : W := mkw 0x0923ba003245f018 0x4248ee800c917c06 0x0003fe00f801f07d 0x0000ff803e007c1f

def z704 : W := mkw 0x137bdcaef8000000 0x04def72bbe000000 0x087ffe0ff8000001 0x821fff83fe000000

def z705 : W := mkw 0x109045fef9200c61 0x8424117fbe480318 0x000001fff8000e72 0x0000007ffe00039c

def z706 : W := mkw 0x0182e160c2618461 0x8060b85830986118 0x9783e180e0e1c671 0x25e0f8603838719c

def z707 : W := mkw 0x1923fe22fa45f018 0x4648ff88be917c06 0x0003fe00f801f07d 0x0000ff803e007c1f

def z708 : W := mkw 0x0182a15043618c61 0x8060a85410d86318 0xf7830180e7e1ce73 0x3de0c06039f8739c

def z709 : W := mkw 0x93ffbbdd771118c5 0x24ffeef75dc44631 0xbbf30180671139cc 0x2efcc06019c44e73

def z710 : W := mkw 0x13dacdeec8000000 0x04f6b37bb2000000 0x138cefff00000002 0x44e33bffc0000000

def z711 : W := mkw 0x0182a15043618c61 0x8060a85410d86318 0x9783018067e0c630 0x25e0c06019f8318c

def z712 : W := mkw 0x13dacdeef8000000 0x04f6b37bbe000000 0x538cfffff8000003 0xd4e33ffffe000000

def z713 : W := mkw 0x167d1c8f3c9e639a 0x459f4723cf2798e6 0x087c1e0f181e318c 0x821f0783c6078c63

def z714 : W := mkw 0x1bebdd66c8cce000 0x06faf759b2333800 0x9fffee7700eec000 0x67fffb9dc03bb000

def z715 : W := mkw 0x06dc01dd05ba0f82 0x01b70077416e83e0 0x3ffc007f07fe0f80 0xcfff001fc1ff83e0

def z716 : W := mkw 0x80042211071118c5 0x2001088441c44631 0x240000000711fffc 0x0900000001c47fff

def z717 : W := mkw 0x800466338f9918c5 0x2001198ce3e64631 0x640cfe7f9fff39cf 0xd9033f9fe7ffce73

def z718 : W := mkw 0x0182e170c3618c61 0x8060b85c30d86318 0xf78fe1ffe7e1ce73 0xfde3f87ff9f8739c

def z719 : W := mkw 0x0182815041608c20 0x8060a05410582308 0xb783018067e0ce30 0x2de0c06019f8338c

def z720 : W := mkw 0x189467eefeddf000 0x062519fbbfb77c00 0x240001fffffff002 0x0900007ffffffc00

def z721 : W := mkw 0x0182a15003618c00 0x0060a85400d86300 0xf783e1f0e7e1ce73 0x7de0f87c39f8739c

def z722 : W := mkw 0x880422110755f8c5 0x2201088441d57e31 0x200000000711f9cc 0x0800000001c47e73

def z723 : W := mkw 0x109045eef8000000 0x0424117bbe000000 0x000ceffff8000002 0x40033bfffe000000

def z724 : W := mkw 0x0b6fba0006ddf000 0x02dbee8001b77c00 0xffffff88ffffffff 0xffffffe23fffffff

def z725 : W := mkw 0x0b6fba0046ddf020 0x82dbee8011b77c08 0xfffffe0067fff031 0xffffff8019fffc0c

def z726 : W := mkw 0x1923fe22fa45f061 0x8648ff88be917c18 0x0003fe00f801f071 0x0000ff803e007c1c

def z727 : W := mkw 0x000064328b010841 0x0000190ca2c04210 0x600cfe7f9f1139cf 0xd8033f9fe7c44e73

def z728 : W := mkw 0x13dacdeef8000000 0x04f6b37bbe000000 0xd38feffff8000003 0x74e3fbfffe000000

def z729 : W := mkw 0x800466338f311ce5 0xa001198ce3cc4739 0x600cfe7f9f113fff 0xd8033f9fe7c44fff

def z730 : W := mkw 0x0021542288000000 0x00085508a2000000 0xc87ffe7f98000003 0xf21fff9fe6000000

def z731 : W := mkw 0x800466338f719ce5 0xa001198ce3dc6739 0xe40ffffffff1ffff 0xf903fffffffc7fff

def z732 : W := mkw 0x13fbddeef8000000 0x04fef77bbe000000 0xfffffffff81e0003 0xfffffffffe078000

def z733 : W := mkw 0x0182c562c8000000 0x0060b158b2000000 0xf78ffffff811ffff 0xfde3fffffe047fff

def z734 : W := mkw 0x8804221107fdfce5 0xa201088441ff7f39 0x2400000007fffffc 0x0900000001ffffff

def z735 : W := mkw 0x0182e572cb618c61 0x8060b95cb2d86318 0xf783e1ffffe1ce73 0x7de0f87ffff8739c

def z736 : W := mkw 0x800466338f719ce5 0xa001198ce3dc6739 0x600cfe7f9ff139cf 0xd8033f9fe7fc4e73

def z737 : W := mkw 0x13fbddeef8046018 0x44fef77bbe011806 0xdbfffffff800c033 0xf6fffffffe00300c

def z738 : W := mkw 0x02d845ee88020300 0x00b6117ba20080c0 0xfffcffff981f3fcf 0xffff3fffe607cff3

def z739 : W := mkw 0x13fbddeef8000000 0x04fef77bbe000000 0x9bffffff78000000 0xe6ffffffde000000

def z740 : W := mkw 0x1102cc22c8000000 0x0440b308b2000000 0x400cfe7f98000003 0xd0033f9fe6000000

def z741 : W := mkw 0x13fbddeef8000000 0x04fef77bbe000000 0xfffffffff811ffff 0xfffffffffe047fff

def z742 : W := mkw 0x13fbddeef8000000 0x04fef77bbe000000 0xdbfffffff801c073 0xf6fffffffe00701c

def z743 : W := mkw 0x0004221107111880 0x0001088441c44620 0x2000000007113980 0x0800000001c44e60

def z744 : W := mkw 0x001044aab8020318 0x4004112aae0080c6 0x400cfffff8000fff 0xd0033ffffe0003ff

def z745 : W := mkw 0x13cacd66c8000000 0x04f2b359b2000000 0x738cfe7f981139cf 0xdce33f9fe6044e73

def z746 : W := mkw 0x0021100000046000 0x0008440000011800 0xec731188f81fffff 0xbb1cc4623e07ffff

def z747 : W := mkw 0x0182e160c2618420 0x8060b85830986108 0xf783e1f0e7e1c633 0x7de0f87c39f8718c

def z748 : W := mkw 0x13cacd66c8000000 0x04f2b359b2000000 0x938feff760000000 0x64e3fbfdd8000000

def z749 : W := mkw 0x80253211071578c5 0x20094c8441c55e31 0xec731000071ff9cd 0xbb1cc40001c7fe73

def z750 : W := mkw 0x13fbddeef8020318 0x44fef77bbe0080c6 0xfffffffff81e0fff 0xfffffffffe0783ff

def z751 : W := mkw 0x80004433890008c5 0x2000110ce2400231 0x600cfe7f981139cf 0xd8033f9fe6044e73

def z752 : W := mkw 0x1123fc22fa45e079 0xc448ff08be91781e 0x0003fe00f801f07d 0x0000ff803e007c1f

def z753 : W := mkw 0x12793c9e3b618c61 0x849e4f278ed86318 0x2c7c1e0f1fe1ce70 0x8b1f0783c7f8739c

def z754 : W := mkw 0x06dc01dd35ba0f9a 0x41b700774d6e83e6 0xfffc11ffffff3fff 0xffff047fffffcfff

def z755 : W := mkw 0x13fbddeef8000000 0x04fef77bbe000000 0x9bffeffff8000002 0x66fffbfffe000000

def z756 : W := mkw 0x06d801dc01aa0f02 0x01b60077006a83c0 0xfffc01ff07ee0e02 0xffff007fc1fb8380

def z757 : W := mkw 0x1182e576cb618c61 0x8460b95db2d86318 0xf783e1f7e7e1ce73 0x7de0f87df9f8739c

def z758 : W := mkw 0x0080215003618c61 0x8020085400d86318 0xf78301f0e7e1ce73 0x7de0c07c39f8739c

def z759 : W := mkw 0x0b6fba0006ddf000 0x02dbee8001b77c00 0xfffffe7f07fff003 0xffffff9fc1fffc00

def z760 : W := mkw 0x0000442288000000 0x00001108a2000000 0x400cfe7f9810318f 0xd0033f9fe6040c63

def z761 : W := mkw 0x075ee0adc6db83e3 0x81d7b82b71b6e0f8 0x087fe00fe01fc1f1 0x821ff803f807f07c

def z762 : W := mkw 0x037bdcaab8066318 0x40def72aae0198c6 0xfffffffff81fffff 0xfffffffffe07ffff

def z763 : W := mkw 0x17fbddeef8220702 0x05fef77bbe0881c0 0xdbfffffff8000603 0xf6fffffffe000180

def z764 : W := mkw 0x0db3bbdd0367ff82 0x036ceef740d9ffe0 0x0003ffff0001ff83 0x0000ffffc0007fe0

def z765 : W := mkw 0x06ed115535bc6c9a 0x41bb44554d6f1b26 0x138f1077ffe1f07d 0x44e3c41dfff87c1f

def z766 : W := mkw 0x06dc01dd05ba0f82 0x01b70077416e83e0 0x9ffc01ff07fe0780 0xe7ff007fc1ff81e0

def z767 : W := mkw 0x149045fff9220f9a 0x4524117ffe4883e6 0x000001fff8000ffe 0x0000007ffe0003ff

def z768 : W := mkw 0x86d867ee8aab1747 0x21b619fba2aac5d1 0x9ff0ff8098ef364d 0x27fc3fe0263bcd93

def z769 : W := mkw 0x1bfbddeef8cee318 0x46fef77bbe33b8c6 0xdffffffff8eec633 0xf7fffffffe3bb18c

def z770 : W := mkw 0x818687434c7094a4 0xa061a1d0d31c2529 0x978f1f8f78f0f7bc 0xa5e3c7e3de3c3def

def z771 : W := mkw 0x13fbddeef8000000 0x04fef77bbe000000 0xdbfcffff18000002 0xf6ff3fffc6000000

def z772 : W := mkw 0x06dc01dd35ba0f9a 0x41b700774d6e83e6 0xfffc01ff1ffe0f8e 0xffff007fc7ff83e3

def z773 : W := mkw 0x80042211071118c5 0x2001088441c44631 0x200010081f1139cc 0x8800040207c44e73

def z774 : W := mkw 0x12795caeb8066318 0x449e572bae0198c6 0xec7ffffff81fffff 0xfb1ffffffe07ffff

def z775 : W := mkw 0x0b6fba0006ddf000 0x02dbee8001b77c00 0xdffffe0007eec001 0xf7ffff8001fbb000

def z776 : W := mkw 0x12795caeb8000000 0x049e572bae000000 0x087cfe7f18000000 0xc21f3f9fc6000000

def z777 : W := mkw 0x0182e160c2618461 0x8060b85830986118 0xf783e180e7e1c671 0x7de0f86039f8719c

def z778 : W := mkw 0x0a4c220006ddf000 0x0293088001b77c00 0xfffcfe0007fff001 0xffff3f8001fffc00

def z779 : W := mkw 0x13cacd66c8000000 0x04f2b359b2000000 0xf78feff7e001ce73 0x7de3fbfdf800739c

def z780 : W := mkw 0x0b6fba0006ddf000 0x02dbee8001b77c00 0xfffffe009ffff04d 0xffffff8027fffc13

def z781 : W := mkw 0x13cacd66c8000000 0x04f2b359b2000000 0xd38ceff700000002 0x74e33bfdc0000000

def z782 : W := mkw 0x0b6fba0006ddf000 0x02dbee8001b77c00 0xfffffe089ffff003 0xffffff8227fffc00

def z783 : W := mkw 0x0182e572cb618c61 0x8060b95cb2d86318 0xf78ffffffff1ffff 0xfde3fffffffc7fff

def z784 : W := mkw 0x13fbddeef866e738 0xc4fef77bbe19b9ce 0xdffffffff8eec633 0xf7fffffffe3bb18c

def z785 : W := mkw 0x80042211071118c5 0x2001088441c44631 0x200000089f1139ce 0x0800000227c44e73

def z786 : W := mkw 0x12484c2688000000 0x04921309a2000000 0x000cee7700000000 0x40033b9dc0000000

def z787 : W := mkw 0x8804221107ddf8c5 0x2201088441f77e31 0x2400000007fff000 0x0900000001fffc00

def z788 : W := mkw 0x13fbddeef8046018 0x44fef77bbe011806 0xfffffffff801fe7f 0xfffffffffe007f9f

def z789 : W := mkw 0x13fbddeef8000000 0x04fef77bbe000000 0xdbffefff60000002 0xf6fffbffd8000000

def z790 : W := mkw 0x06dc01dd35ba0f9a 0x41b700774d6e83e6 0xffff01ffffffcfff 0xffffc07ffffff3ff

def z791 : W := mkw 0x80353299371118c5 0x200d4ca64dc44631 0xe8731188ff1139cf 0xba1cc4623fc44e73

def z792 : W := mkw 0x800446338d101884 0x2001118ce3440621 0x600cfe7f9f10398f 0xd8033f9fe7c40e63

def z793 : W := mkw 0x0ffb99cc00eee702 0x03fee673003bb9c0 0xdfffffff00eec603 0xf7ffffffc03bb180

def z794 : W := mkw 0x0182e572cb618c61 0x8060b95cb2d86318 0xf78feff7e7e1ce73 0x7de3fbfdf9f8739c

def z795 : W := mkw 0x0b6fba0006ddf000 0x02dbee8001b77c00 0x9ff3000007eec000 0x27fcc00001fbb000

def z796 : W := mkw 0x0102c42288000000 0x0040b108a2000000 0xd38ffe7f98000003 0xf4e3ff9fe6000000

def z797 : W := mkw 0x01b3f1f8f367ef79 0xc06cfc7e3cd9fbde 0x1bf0f0781ffe318c 0xc6fc3c1e07ff8c63

def z798 : W := mkw 0x0080456288000000 0x00201158a2000000 0xd38cffff98000003 0xf4e33fffe6000000

def z799 : W := mkw 0x17fbddeef8ae671a 0x45fef77bbe2b99c6 0xfffffffff8ffffff 0xfffffffffe3fffff

def z800 : W := mkw 0x06dc01dd05ba0f82 0x01b70077416e83e0 0xfffc01ff07ff3fce 0xffff007fc1ffcff3

def z801 : W := mkw 0x10215c22b8000000 0x04085708ae000000 0x400cfe7f98000003 0xd0033f9fe6000000

def z802 : W := mkw 0x0182e171c3618ce1 0x8060b85c70d86338 0xf783e1ffe7e1cff3 0x7de0f87ff9f873fc

def z803 : W := mkw 0x0000442288000000 0x00001108a2000000 0x400cee7780000003 0x50033b9de0000000

def z804 : W := mkw 0x06cc015505ba0f82 0x01b30055416e83e0 0xfffc007707fe0f80 0xffff001dc1ff83e0

def z805 : W := mkw 0x13cacd66c8066318 0x44f2b359b20198c6 0x378cee77001ffffc 0x4de33b9dc007ffff

def z806 : W := mkw 0x13ebdd66f8000000 0x04faf759be000000 0x538ffe7ff8000003 0xd4e3ff9ffe000000

def z807 : W := mkw 0x8404221107bf7fdf 0x6101088441efdff7 0x2400000007fffffc 0x0900000001ffffff

def z808 : W := mkw 0x06dc01dd05ba0f82 0x01b70077416e83e0 0xfffc11ff9ffe0f83 0xffff047fe7ff83e0

def z809 : W := mkw 0x06dc01dd05ba0f82 0x01b70077416e83e0 0xdffc01ff07ee0602 0xf7ff007fc1fb8180

def z810 : W := mkw 0x13ebdd66f8000000 0x04faf759be000000 0x138cfe7718000000 0x44e33f9dc6000000

def z811 : W := mkw 0x17cacd66c8a80402 0x05f2b359b22a0100 0x138cee7700e00000 0x44e33b9dc0380000

def z812 : W := mkw 0x8182e772cb619c65 0xa060b9dcb2d86719 0xf78fffffffe1fe7f 0xfde3fffffff87f9f

def z813 : W := mkw 0x02dc01dd05980880 0x00b7007741660220 0xfffc01ff07fe0982 0xffff007fc1ff8260

def z814 : W := mkw 0x13ebdd66c8000000 0x04faf759b2000000 0xdbfffff7e0000003 0xf6fffffdf8000000

def z815 : W := mkw 0x80042211071118c5 0x2001088441c44631 0x000000000710318c 0x0000000001c40c63

def z816 : W := mkw 0x80042211079918c5 0x2001088441e64631 0x2400000007ff39cc 0x0900000001ffce73

def z817 : W := mkw 0x0b6bb80002cde000 0x02daee0000b37800 0xfffffe0007efc001 0xffffff8001fbf000

def z818 : W := mkw 0x80042211071118c5 0x2001088441c44631 0x60000008071139ce 0x9800000201c44e73

def z819 : W := mkw 0x800446238c101084 0x20011188e3040421 0x600cfe7f981139cf 0xd8033f9fe6044e73

def z820 : W := mkw 0x13ebdd66c8000000 0x04faf759b2000000 0x138ffe7700000001 0x44e3ff9dc0000000

def z821 : W := mkw 0x109045fef9220f79 0xc424117fbe4883de 0x000001fff8000ffe 0x0000007ffe0003ff

def z822 : W := mkw 0x8004221107719ce5 0xa001088441dc6739 0xe4031188fff1ffff 0xb900c4623ffc7fff

def z823 : W := mkw 0x1527dc33fdba0f82 0x0549f70cff6e83e0 0x2403fe00fffe0f81 0x0900ff803fff83e0

def z824 : W := mkw 0x0b6fba0006ddf000 0x02dbee8001b77c00 0xfffffe081ffff18d 0xffffff8207fffc63

def z825 : W := mkw 0x0182c562c8000000 0x0060b158b2000000 0xd38feff7e0000003 0x74e3fbfdf8000000

def z826 : W := mkw 0x049001dd01220f82 0x01240077404883e0 0xfff001ff07fe0f82 0xfffc007fc1ff83e0

def z827 : W := mkw 0x06dc01dd05ba0f82 0x01b70077416e83e0 0xbffc01f707fe0f80 0x6fff007dc1ff83e0

def z828 : W := mkw 0x800466338f1118c5 0x2001198ce3c44631 0x600cfe7f1f10398e 0xd8033f9fc7c40e63

def z829 : W := mkw 0x0c04221107fdfc82 0x0301088441ff7f20 0x2400000007fff000 0x0900000001fffc00

def z830 : W := mkw 0x0b5eaa8836db9318 0x42d7aaa20db6e4c6 0x138cef88ffe00ffe 0x44e33be23ff803ff

def z831 : W := mkw 0x0b6fba0006ddf000 0x02dbee8001b77c00 0xffffff80e7fff003 0xffffffe039fffc00

def z832 : W := mkw 0x0000000000000000 0x0000000000000000 0x600c007f00100982 0xd803001fc0040260

def z833 : W := mkw 0x8182e171c3618ce5 0xa060b85c70d86339 0xf783e1f0e7e1cfff 0x7de0f87c39f873ff

def z834 : W := mkw 0x800466338f1118c5 0x2001198ce3c44631 0x000cfe7f9f0139cf 0x40033f9fe7c04e73

def z835 : W := mkw 0x13fbddeef8000000 0x04fef77bbe000000 0x1bfcfffff8000002 0xc6ff3ffffe000000

def z836 : W := mkw 0x03fb99cc30000000 0x00fee6730c000000 0xdbfffffff8000003 0xf6fffffffe000000

def z837 : W := mkw 0x1bfbddeef88c6000 0x06fef77bbe231800 0xdbfffffff80e0003 0xf6fffffffe038000

def z838 : W := mkw 0x13fbddeef8200400 0x04fef77bbe080100 0xdffffffff8e00603 0xf7fffffffe380180

def z839 : W := mkw 0x800446338d1018c5 0x2001118ce3440631 0x400cfe7f981039cf 0xd0033f9fe6040e73

def z840 : W := mkw 0x0182a15043618c61 0x8060a85410d86318 0xf78301f067e1ce72 0x7de0c07c19f8739c

def z841 : W := mkw 0x0c04221107ffff9a 0x4301088441ffffe6 0x2400000007fffffc 0x0900000001ffffff

def z842 : W := mkw 0x13cacd66c8000000 0x04f2b359b2000000 0x138ceff7e0000002 0x44e33bfdf8000000

def z843 : W := mkw 0x8b6bdc3389cce8c5 0x22daf70ce2733a31 0x9ff3007f98eec9ce 0x27fcc01fe63bb273

def z844 : W := mkw 0x0aed5b70c5bc7c61 0x82bb56dc316f1f18 0x087c1ff0e01e3e72 0x821f07fc38078f9c

def z845 : W := mkw 0x02f955eeb8066318 0x40be557bae0198c6 0xfffffffff81fffff 0xfffffffffe07ffff

def z846 : W := mkw 0x0b6fba0006ddf000 0x02dbee8001b77c00 0xbff3fe0007fff001 0x2ffcff8001fffc00

def z847 : W := mkw 0x8004221107719ce5 0xa001088441dc6739 0x2000000007f139cc 0x0800000001fc4e73

def z848 : W := mkw 0x13fbddeef8046000 0x04fef77bbe011800 0xfffffffff81ffe73 0xfffffffffe07ff9c

def z849 : W := mkw 0x009045ee88000000 0x0024117ba2000000 0x400cffff98000003 0xd0033fffe6000000

def z850 : W := mkw 0x1133dcaaf8066318 0x444cf72abe0198c6 0xec7ffffff81fffff 0xfb1ffffffe07ffff

def z851 : W := mkw 0x800466338f1118c5 0x2001198ce3c44631 0xf78cfe7f9ff139cf 0xfde33f9fe7fc4e73

def z852 : W := mkw 0x02cc015105b80c80 0x00b30054416e0320 0xfffc01ff07fe0f82 0xffff007fc1ff83e0

def z853 : W := mkw 0x0031108830066318 0x400c44220c0198c6 0xac730188f81ffffe 0x2b1cc0623e07ffff

def z854 : W := mkw 0x11b3ddeef8000000 0x046cf77bbe000000 0x400ffffff8000003 0xd003fffffe000000

def z855 : W := mkw 0x0b4eaa0006d99000 0x02d3aa8001b66400 0x1bfcee0007fe0000 0xc6ff3b8001ff8000

def z856 : W := mkw 0x1102cc22c8000000 0x0440b308b2000000 0x000cee7700000000 0x40033b9dc0000000

def z857 : W := mkw 0x0182e170c3618c61 0x8060b85c30d86318 0xf783f1f0e7f1fe73 0xfde0fc7c39fc7f9c

def z858 : W := mkw 0x0182e170c3618c61 0x8060b85c30d86318 0xf783e1f067e0ce32 0x7de0f87c19f8338c

def z859 : W := mkw 0x06dc01dd05b80c82 0x01b70077416e0320 0xfffc01ff07fe0002 0xffff007fc1ff8000

def z860 : W := mkw 0x13fb99cc7066e738 0xc4fee6731c19b9ce 0x9ff3018060eec630 0x27fcc060183bb18c

def z861 : W := mkw 0x06dc01dd05ba0f82 0x01b70077416e83e0 0x7bfc007f07fe0982 0xdeff001fc1ff8260

def z862 : W := mkw 0x02d801cc00000000 0x00b6007300000000 0xdbfcffff00000003 0xf6ff3fffc0000000

def z863 : W := mkw 0x036f9800049c6000 0x00dbe60001271800 0xfffffe0007fff001 0xffffff8001fffc00

def z864 : W := mkw 0x17fb99cc70ae671a 0x45fee6731c2b99c6 0x9ff3018060eec630 0x27fcc060183bb18c

def z865 : W := mkw 0x13fbddeef8000000 0x04fef77bbe000000 0x9bfffff7f8000001 0x66fffffdfe000000

def z866 : W := mkw 0x000444338d100880 0x0001110ce3440220 0x600cfe7f9f1139cf 0xd8033f9fe7c44e73

def z867 : W := mkw 0x000466228e111000 0x00011988a3844400 0x600cfe7f9f1139cf 0xd8033f9fe7c44e73

def z868 : W := mkw 0x02dc01cc049a0300 0x00b70073012680c0 0xfffc01ff07fe0f82 0xffff007fc1ff83e0

def z869 : W := mkw 0x0182c170c1200c00 0x0060b05c30480300 0xf783e1f0e7e1ce73 0x7de0f87c39f8739c

def z870 : W := mkw 0x1192c5eef8000000 0x0464b17bbe000000 0xd38ffffff8000003 0xf4e3fffffe000000

def z871 : W := mkw 0x0b6f980004dce000 0x02dbe60001373800 0xfffffe0007fec001 0xffffff8001ffb000

def z872 : W := mkw 0x0182815041608c20 0x8060a05410582308 0xf78301f0e7e1ce73 0x7de0c07c39f8739c

def z873 : W := mkw 0x80042211071578dd 0x6001088441c55e37 0x200000000711f9fc 0x0800000001c47e7f

def z874 : W := mkw 0x0182e170c3618c61 0x8060b85c30d86318 0xd783e1f0e7e0c633 0x75e0f87c39f8318c

def z875 : W := mkw 0x03ca894400000000 0x00f2a25100000000 0x138cee7700000000 0x44e33b9dc0000000

def z876 : W := mkw 0x049045ff89220f82 0x0124117fe24883e0 0x000001ff98000f82 0x0000007fe60003e0

def z877 : W := mkw 0x8a7d1e8b3c9e739c 0x629f47a2cf279ce7 0x087c1e0f181e318c 0x821f0783c6078c63

def z878 : W := mkw 0x03da89cc00000000 0x00f6a27300000000 0xdbfcefff00000002 0xf6ff3bffc0000000

def z879 : W := mkw 0x867d168f3c9e739e 0x619f45a3cf279ce7 0x087c1e0f181e318c 0x821f0783c6078c63

def z880 : W := mkw 0x800466338f1118c5 0x2001198ce3c44631 0x640cfe7f9f11ffff 0xd9033f9fe7c47fff

def z881 : W := mkw 0x1bfb99cc70cee318 0x46fee6731c33b8c6 0x9ff3018060eec630 0x27fcc060183bb18c

def z882 : W := mkw 0x8404221107bb1fc7 0x2101088441eec7f1 0x2400000007fe0f80 0x0900000001ff83e0

def z883 : W := mkw 0x13ebdd66f8046018 0x44faf759be011806 0x138ffe77f801f07d 0x44e3ff9dfe007c1f

def z884 : W := mkw 0x0b6ffe228eddf000 0x02dbff88a3b77c00 0xfffffe7f9ffff9cf 0xffffff9fe7fffe73

def z885 : W := mkw 0x800466338f1118c5 0x2001198ce3c44631 0x000cfe7f981139cf 0x80033f9fe6044e73

def z886 : W := mkw 0x0182e370c3619c61 0x8060b8dc30d86718 0xf783fff0e7e1fe73 0x7de0fffc39f87f9c

def z887 : W := mkw 0x0b6fba0006ddf000 0x02dbee8001b77c00 0xbfffee0007fff000 0x6ffffb8001fffc00

def z888 : W := mkw 0x80042211071118c5 0x2001088441c44631 0x200010009f1139cd 0x0800040027c44e73

def z889 : W := mkw 0x0b6fba0006ddf000 0x02dbee8001b77c00 0x1bfcee0007ee0000 0x46ff3b8001fb8000

def z890 : W := mkw 0x009401d905320f80 0x00250076414c83e0 0xfffc01ff07fe0f82 0xffff007fc1ff83e0

def z891 : W := mkw 0x800066228a011045 0x20001988a2804411 0x600cfe7f981139cf 0xd8033f9fe6044e73

def z892 : W := mkw 0x0000442288000000 0x00001108a2000000 0x000cee7f98000002 0x40033b9fe6000000

def z893 : W := mkw 0x13fbddeef8000000 0x04fef77bbe000000 0xdbfffff760000001 0xf6fffffdd8000000

def z894 : W := mkw 0x003154aab8066318 0x400c552aae0198c6 0xcc7ffffff80ec633 0xf31ffffffe03b18c

def z895 : W := mkw 0x03ebdd62c8000000 0x00faf758b2000000 0xdbfffffff8000003 0xf6fffffffe000000

def z896 : W := mkw 0x0000040208000000 0x0000010082000000 0x000c1e0f1810318c 0x80030783c6040c63

def z897 : W := mkw 0x13fbddeef8046018 0x44fef77bbe011806 0xfbfffffff811f9ff 0xfefffffffe047e7f

def z898 : W := mkw 0x849045ffc9220fe7 0xa124117ff24883f9 0x000001fff8000ffe 0x0000007ffe0003ff

def z899 : W := mkw 0x101044aeb8000000 0x0404112bae000000 0x400cfe7f98000003 0xd0033f9fe6000000

def z900 : W := mkw 0x949045fff9220fc7 0x2524117ffe4883f1 0x000001fff8000fce 0x0000007ffe0003f3

def z901 : W := mkw 0x06dc01dd05ba0f82 0x01b70077416e83e0 0xdbfc01ff07fe0182 0xf6ff007fc1ff8060

def z902 : W := mkw 0x0000442288000000 0x00001108a2000000 0xe40ffffff801ce73 0xf903fffffe00739c

def z903 : W := mkw 0x13fbddeef8000000 0x04fef77bbe000000 0xdbffeff7e0000003 0x76fffbfdf8000000

def z904 : W := mkw 0x003154aab8066318 0x400c552aae0198c6 0x487cfe7f981e318f 0xd21f3f9fe6078c63

def z905 : W := mkw 0x1bfbddeef8cce000 0x06fef77bbe333800 0xfffffffff8fff003 0xfffffffffe3ffc00

def z906 : W := mkw 0x0182c562c8608420 0x8060b158b2182108 0xd78ffffff8e0c633 0xf5e3fffffe38318c

def z907 : W := mkw 0x13ebdd66f8000000 0x04faf759be000000 0x138fee7760000000 0x44e3fb9dd8000000

def z908 : W := mkw 0x13fbddeef8000018 0x44fef77bbe000006 0xdbfffffff800007f 0xf6fffffffe00001f

def z909 : W := mkw 0x840466338fb91cc7 0x2101198ce3ee4731 0x600cfe7f9ff139cf 0xd8033f9fe7fc4e73

def z910 : W := mkw 0x9923fe22fa45f045 0x2648ff88be917c11 0x0003fe00f801f04d 0x0000ff803e007c13

def z911 : W := mkw 0x0982eb70c3619c61 0x8260badc30d86718 0xf783eff0e7e1ce73 0x7de0fbfc39f8739c

def z912 : W := mkw 0x849045ff89220fc7 0x2124117fe24883f1 0x000001ff00000f82 0x0000007fc00003e0

def z913 : W := mkw 0x8804221107dffbdd 0x6201088441f7fef7 0x2400000007fffffc 0x0900000001ffffff

def z914 : W := mkw 0x06dc01cc04ba0702 0x01b70073012e81c0 0xfffc01ff07fe0602 0xffff007fc1ff8180

def z915 : W := mkw 0x800422110777fffd 0xe001088441ddffff 0x2400000007fffffc 0x0900000001ffffff

def z916 : W := mkw 0x10804566c8000000 0x04201159b2000000 0x400cfe7f98000003 0xd0033f9fe6000000

def z917 : W := mkw 0x0004221107111880 0x0001088441c44620 0x600cfe7f9f1139cf 0xd8033f9fe7c44e73

def z918 : W := mkw 0x80042211071118c5 0x2001088441c44631 0x60001000071139cd 0x9800040001c44e73

def z919 : W := mkw 0x8404221107b91cc7 0x2101088441ee4731 0x0000000007e00000 0x0000000001f80000

def z920 : W := mkw 0x1bfbddeef8cee318 0x46fef77bbe33b8c6 0xfffffffff8ffffff 0xfffffffffe3fffff

def z921 : W := mkw 0x13fbddeef8000000 0x04fef77bbe000000 0x087ffffff8000003 0x821ffffffe000000

def z922 : W := mkw 0x800466338f1118c5 0x2001198ce3c44631 0x400cfe7f9f10318f 0xd0033f9fe7c40c63

def z923 : W := mkw 0x036bb8000245e000 0x00daee0000917800 0xfffffe0007fff001 0xffffff8001fffc00

def z924 : W := mkw 0x0031108830066318 0x400c44220c0198c6 0xfff31188ffffffff 0xfffcc4623fffffff

def z925 : W := mkw 0x13dacdeef8000000 0x04f6b37bbe000000 0x138ceff760000000 0x44e33bfdd8000000

def z926 : W := mkw 0x0182e170c3618c61 0x8060b85c30d86318 0xf783e1f067e1c631 0x7de0f87c19f8718c

def z927 : W := mkw 0x0182c562c8000000 0x0060b158b2000000 0x138cee7700000000 0x44e33b9dc0000000

def z928 : W := mkw 0x0b6fba0006ddf000 0x02dbee8001b77c00 0xfffffe00e7fff071 0xffffff8039fffc1c

def z929 : W := mkw 0x80042211071118c5 0x2001088441c44631 0x60000000871139cf 0x1800000021c44e73

def z930 : W := mkw 0x0182e160c2418000 0x0060b85830906000 0xf783e1f0e7e1ce73 0x7de0f87c39f8739c

def z931 : W := mkw 0x13fbddeef8200420 0x84fef77bbe080108 0xdbfffffff8000633 0xf6fffffffe00018c

def z932 : W := mkw 0x0b6fba0036ddf000 0x02dbee800db77c00 0xfffffe00fffff001 0xffffff803ffffc00

def z933 : W := mkw 0x1bcacd66c8c88000 0x06f2b359b2322000 0x138cee7700e00000 0x44e33b9dc0380000

def z934 : W := mkw 0x13fbddeef866e738 0xc4fef77bbe19b9ce 0xfffffffff8ffffff 0xfffffffffe3fffff

def z935 : W := mkw 0x8b6fba0006ddf045 0x22dbee8001b77c11 0xfffffe0007fff04d 0xffffff8001fffc13

def z936 : W := mkw 0x0182e170c3618c61 0x8060b85c30d86318 0xb78301f0e7e1ce72 0x2de0c07c39f8739c

def z937 : W := mkw 0x0edc0bdd05ba1f82 0x03b702f7416e87e0 0xfffc0fff07fe0f82 0xffff03ffc1ff83e0

def z938 : W := mkw 0x02d801dc01220f00 0x00b60077004883c0 0xfffc01ff07fe0f82 0xffff007fc1ff83e0

def z939 : W := mkw 0x0c04221107ffffe3 0x8301088441fffff8 0x2400000007fffff0 0x0900000001fffffc

def z940 : W := mkw 0x0102c422c8000000 0x0040b108b2000000 0x400ffe7ff8000003 0xd003ff9ffe000000

def z941 : W := mkw 0x800466338f1118c5 0x2001198ce3c44631 0xec7cfe7f9f1f39cf 0xfb1f3f9fe7c7ce73

def z942 : W := mkw 0x00804562c8000000 0x00201158b2000000 0x400cfffff8000003 0xd0033ffffe000000

def z943 : W := mkw 0x0b6fba0006ddf000 0x02dbee8001b77c00 0xffffff8067fff631 0xffffffe019fffd8c

def z944 : W := mkw 0x0102e020c2418061 0x8040b80830906018 0xf783e180e7e1ce73 0x7de0f86039f8739c

def z945 : W := mkw 0x1a7d1e8e3c9e7318 0x469f47a38f279cc6 0x087c1e0f181e318c 0x821f0783c6078c63

def z946 : W := mkw 0x13ebdd66c8000000 0x04faf759b2000000 0xdbfffe7f98000003 0xf6ffff9fe6000000

def z947 : W := mkw 0x8804221107d998c5 0x2201088441f66631 0x0000000007e00000 0x0000000001f80000

def z948 : W := mkw 0x13fbddeef8066300 0x04fef77bbe0198c0 0xfffffffff81fff83 0xfffffffffe07ffe0

def z949 : W := mkw 0x13cacd66c8608420 0x84f2b359b2182108 0x138cee7700e00000 0x44e33b9dc0380000

def z950 : W := mkw 0x8000442288000045 0x20001108a2000011 0x400cfe7f9800004f 0xd0033f9fe6000013

def z951 : W := mkw 0x03fb99cc00066300 0x00fee673000198c0 0xffffffff001fff83 0xffffffffc007ffe0

def z952 : W := mkw 0x06dc01dd05ba0f82 0x01b70077416e83e0 0xfffc01f707ee0e02 0x7fff007dc1fb8380

def z953 : W := mkw 0x149045fff9220fe3 0x8524117ffe4883f8 0x000001fff8000ff2 0x0000007ffe0003fc

def z954 : W := mkw 0x13dacdeec8000000 0x04f6b37bb2000000 0xdbfcffff98000003 0xf6ff3fffe6000000

def z955 : W := mkw 0x13fbddeef8020300 0x04fef77bbe0080c0 0xdffffffff80e0603 0xf7fffffffe038180

def z956 : W := mkw 0x01b3d5eaf8066318 0x406cf57abe0198c6 0xfffffffff81fffff 0xfffffffffe07ffff

def z957 : W := mkw 0x02695c2288000000 0x009a5708a2000000 0x487cfe7f98000003 0xd21f3f9fe6000000

def z958 : W := mkw 0x17dacdeec8aa0702 0x05f6b37bb22a81c0 0x9ffceff700ee0600 0x67ff3bfdc03b8180

def z959 : W := mkw 0x0102a00002418000 0x0040a80000906000 0xf783e18067e1c631 0x7de0f86019f8718c

def z960 : W := mkw 0x13cacd66c8000000 0x04f2b359b2000000 0x138cfe7f18000000 0xc4e33f9fc6000000

def z961 : W := mkw 0x024c000004980000 0x0093000001260000 0xfffc007f07fe0002 0xffff001fc1ff8000

def z962 : W := mkw 0x17fbddeef8ea8722 0x85fef77bbe3aa1c8 0xdffffffff8eec633 0xf7fffffffe3bb18c

def z963 : W := mkw 0x0031108830066318 0x400c44220c0198c6 0x08731188f81fffff 0x821cc4623e07ffff

def z964 : W := mkw 0x06dc01dd05ba0f82 0x01b70077416e83e0 0x1bfc01ff07fe0f82 0xc6ff007fc1ff83e0

def z965 : W := mkw 0x0182814040608420 0x8060a05010182108 0xf783018067e0c630 0x7de0c06019f8318c

def z966 : W := mkw 0x00215422b8046018 0x40085508ae011806 0x400ffe7ff801f07f 0xd003ff9ffe007c1f

def z967 : W := mkw 0x800446238c101084 0x20011188e3040421 0x000cfe7f1810318c 0xc0033f9fc6040c63

def z968 : W := mkw 0x03fbd9ecc0000000 0x00fef67b30000000 0xdbffffffe0000003 0xf6fffffff8000000

def z969 : W := mkw 0x0182e170c3618c61 0x8060b85c30d86318 0xfff3e1f0e7ffce73 0xfffcf87c39fff39c

def z970 : W := mkw 0x0031108830066318 0x400c44220c0198c6 0xac731180f81ffffd 0x2b1cc4603e07ffff

def z971 : W := mkw 0x13cacd66c8000000 0x04f2b359b2000000 0x138cee7f98000002 0x44e33b9fe6000000

def z972 : W := mkw 0x8404221107b91cc7 0x2101088441ee4731 0x2000000007f139cc 0x0800000001fc4e73

def z973 : W := mkw 0x13fbddeef8408000 0x04fef77bbe102000 0xdffffffff8e0c003 0xf7fffffffe383000

def z974 : W := mkw 0x0923ba000245f000 0x0248ee8000917c00 0xfff3fe0007fff001 0xfffcff8001fffc00

def z975 : W := mkw 0x06dc45ff8dba0f82 0x01b7117fe36e83e0 0xfffcffff9fff3fcf 0xffff3fffe7ffcff3

def z976 : W := mkw 0x0182c562c8000000 0x0060b158b2000000 0x538cfe7f98000003 0xd4e33f9fe6000000

def z977 : W := mkw 0x13ebdd66c8046000 0x04faf759b2011800 0xfffffe77001ff001 0xffffff9dc007fc00

def z978 : W := mkw 0x803532993777fffd 0xe00d4ca64dddffff 0xec731188ffffffff 0xbb1cc4623fffffff

def z979 : W := mkw 0x13fbddeef8020300 0x04fef77bbe0080c0 0xdbfffffff81e0183 0xf6fffffffe078060

def z980 : W := mkw 0x0b6fba0006ddf000 0x02dbee8001b77c00 0xfffffe0007fff9cd 0xffffff8001fffe73

def z981 : W := mkw 0x800466338f5198c5 0x2001198ce3d46631 0x640cfe7f9ff1f9cf 0xd9033f9fe7fc7e73

def z982 : W := mkw 0x001044aa88020300 0x0004112aa20080c0 0xec7cffff981e0f83 0xfb1f3fffe60783e0

def z983 : W := mkw 0x02cc014404980000 0x00b3005101260000 0xfffc007707fe0000 0xffff001dc1ff8000

def z984 : W := mkw 0x0b6f9a00049c7000 0x02dbe68001271c00 0xfffffe0007fe3001 0xffffff8001ff8c00

def z985 : W := mkw 0x0182e170c3618c61 0x8060b85c30d86318 0xb783e1f067e1ce70 0x6de0f87c19f8739c

def z986 : W := mkw 0x0c35329907ffff82 0x030d4ca641ffffe0 0xec73118807ffff83 0xbb1cc46201ffffe0

def z987 : W := mkw 0x036fb80006d98000 0x00dbee0001b66000 0xfffffe0007ffc001 0xffffff8001fff000

def z988 : W := mkw 0x036b980000000000 0x00dae60000000000 0xdbfffe7f00000003 0xf6ffff9fc0000000

def z989 : W := mkw 0x06dc01dd05ba0f82 0x01b70077416e83e0 0xfffc01ff87ff0fc3 0xffff007fe1ffc3f0

def z990 : W := mkw 0x0182a14042618420 0x8060a85010986108 0xf783e180e7e1ce73 0x7de0f86039f8739c

def z991 : W := mkw 0x8825321107ddf8c5 0x22094c8441f77e31 0xec7310089ffff9cf 0xbb1cc40227fffe73

def z992 : W := mkw 0x0182e170c3618c61 0x8060b85c30d86318 0xf78ffff0e7e1ce73 0xfde3fffc39f8739c

def z993 : W := mkw 0x8004221107719ce5 0xa001088441dc6739 0x2400000007e1ce70 0x0900000001f8739c

def z994 : W := mkw 0x8014229937131bdd 0x600508a64dc4c6f7 0x20000188ff113ffe 0x080000623fc44fff

def z995 : W := mkw 0x800466338f1118c5 0x2001198ce3c44631 0x200cfe7f1f1139cc 0xc8033f9fc7c44e73

def z996 : W := mkw 0x06cc015505b80c82 0x01b30055416e0320 0xfffc01f707fe0e02 0xffff007dc1ff8380

def z997 : W := mkw 0x8804221107d998c5 0x2201088441f66631 0x2000000007f139cc 0x0800000001fc4e73

def z998 : W := mkw 0x024c000004980000 0x0093000001260000 0xfffcfe0007fe0001 0xffff3f8001ff8000

def z999 : W := mkw 0x8923fe22ca45f065 0xa248ff88b2917c19 0x0003fe00f801f07d 0x0000ff803e007c1f

def z1000 : W := mkw 0x0182e170c3618c61 0x8060b85c30d86318 0x9783e1f0e7e1c671 0x65e0f87c39f8719c

def z1001 : W := mkw 0x03eb994400000000 0x00fae65100000000 0xdbfffe7700000001 0xf6ffff9dc0000000

def z1002 : W := mkw 0x12f95deeb8000000 0x04be577bae000000 0xdbfcffff98000003 0xf6ff3fffe6000000

def z1003 : W := mkw 0x8182e572cb618c65 0xa060b95cb2d86319 0xf783e1f0ffe1ce7f 0x7de0f87c3ff8739f

def z1004 : W := mkw 0x13cacd66c8000000 0x04f2b359b2000000 0x538cee7f00000002 0xd4e33b9fc0000000

def z1005 : W := mkw 0x0b6fba0006ddf061 0x82dbee8001b77c18 0xfffffe0007fff071 0xffffff8001fffc1c

def z1006 : W := mkw 0x1182ed72cb618c61 0x8460bb5cb2d86318 0xf783eff0e7e1ce73 0x7de0fbfc39f8739c

def z1007 : W := mkw 0x803576bbbf177bdd 0x600d5daeefc5def7 0x8c7feff7670ec630 0x631ffbfdd9c3b18c

def z1008 : W := mkw 0x13fbddeef8000061 0x84fef77bbe000018 0xdbfffffff8000073 0xf6fffffffe00001c

def z1009 : W := mkw 0x13fbddeef8020318 0x44fef77bbe0080c6 0xdbfffffff800018f 0xf6fffffffe000063

def z1010 : W := mkw 0x13fbddeef8608420 0x84fef77bbe182108 0xfffffffff8e1ce73 0xfffffffffe38739c

def z1011 : W := mkw 0x13fbddeef8046000 0x04fef77bbe011800 0xdbfffffff801f003 0xf6fffffffe007c00

def z1012 : W := mkw 0x0ffb99cc30eee71a 0x43fee6730c3bb9c6 0x9ff3018060eec630 0x27fcc060183bb18c

def z1013 : W := mkw 0x0000442288000000 0x00001108a2000000 0x000cfe7798000001 0x40033f9de6000000

def z1014 : W := mkw 0x026d3200069d7000 0x009b4c8001a75c00 0xfffffe0007fff001 0xffffff8001fffc00

def z1015 : W := mkw 0x10b155eef8066318 0x442c557bbe0198c6 0xec7ffffff81fffff 0xfb1ffffffe07ffff

def z1016 : W := mkw 0x13fbddeef8066318 0x44fef77bbe0198c6 0xfffffffff81e3f8f 0xfffffffffe078fe3

def z1017 : W := mkw 0x137bdcaeb8000000 0x04def72bae000000 0xdbfffe7f98000003 0xf6ffff9fe6000000

def z1018 : W := mkw 0x0fffbbdd07ffff82 0x03ffeef741ffffe0 0xbff3018007ffff80 0x2ffcc06001ffffe0

def z1019 : W := mkw 0x8923fe228a45f045 0x2248ff88a2917c11 0x0003fe000001f001 0x0000ff8000007c00

def z1020 : W := mkw 0x800466338f1118c5 0x2001198ce3c44631 0xe40cffff9f113fcf 0xf9033fffe7c44ff3

def z1021 : W := mkw 0x034e880004980000 0x00d3a20001260000 0xfffcee0007fe0000 0xffff3b8001ff8000

def z1022 : W := mkw 0x0b6bba0002cdf000 0x02daee8000b37c00 0xfff3fe0007eff001 0x7ffcff8001fbfc00

def z1023 : W := mkw 0x13fbddeef8066318 0x44fef77bbe0198c6 0xdbfffffff801ffff 0xf6fffffffe007fff

def z1024 : W := mkw 0x13fbddeef8000000 0x04fef77bbe000000 0xdbfffe7f18000001 0xf6ffff9fc6000000

def z1025 : W := mkw 0x10804566c8000000 0x04201159b2000000 0x000cee7700000000 0x40033b9dc0000000

def z1026 : W := mkw 0x0182e170c3618c61 0x8060b85c30d86318 0x9783e1f0e7e0ce72 0x65e0f87c39f8339c

def z1027 : W := mkw 0x880466338fd998c5 0x2201198ce3f66631 0x600cfe7f9ff139cf 0xd8033f9fe7fc4e73

def z1028 : W := mkw 0x0b4eaa0006d99000 0x02d3aa8001b66400 0xfffcfe0007ff3001 0xffff3f8001ffcc00

def z1029 : W := mkw 0x0000442288000000 0x00001108a2000000 0x0000007f980009ce 0x0000001fe6000273

def z1030 : W := mkw 0x13cacd66c8000000 0x04f2b359b2000000 0xd38fee7700000001 0x74e3fb9dc0000000

def z1031 : W := mkw 0x1ffbddeef8eee702 0x07fef77bbe3bb9c0 0xdffffffff8eec603 0xf7fffffffe3bb180

def z1032 : W := mkw 0x0182e170c3618c61 0x8060b85c30d86318 0xf783f1f8ffe1ce73 0xfde0fc7e3ff8739c

def z1033 : W := mkw 0x06dc01dd05ba0f82 0x01b70077416e83e0 0x1bfc007707ee0000 0x46ff001dc1fb8000

def z1034 : W := mkw 0x800466338f1118c5 0x2001198ce3c44631 0xe40ffe7f9f11f9cf 0xf903ff9fe7c47e73

def z1035 : W := mkw 0x13fbddeef8000000 0x04fef77bbe000000 0xdbfffffff810318f 0xf6fffffffe040c63

def z1036 : W := mkw 0x036fba0006991000 0x00dbee8001a64400 0xfffffe0007ff3001 0xffffff8001ffcc00

def z1037 : W := mkw 0x1923fe22ca45f000 0x0648ff88b2917c00 0x0003fe000001f001 0x0000ff8000007c00

def z1038 : W := mkw 0x06dc03dd05ba1f82 0x01b700f7416e87e0 0xfffc1fff07fe3f82 0xffff07ffc1ff8fe0

def z1039 : W := mkw 0x0404221107bb1f82 0x0101088441eec7e0 0x2400000007ff3f80 0x0900000001ffcfe0

def z1040 : W := mkw 0x06dc01dd05ba0f82 0x01b70077416e83e0 0xffff01ffe7fe0f83 0xffffc07ff9ff83e0

def z1041 : W := mkw 0x13dacdeef8000000 0x04f6b37bbe000000 0xdbfceffff8000002 0xf6ff3bfffe000000

def z1042 : W := mkw 0x86dc01dd05ba0fc7 0x21b70077416e83f1 0xfffc01ff07fe0fce 0xffff007fc1ff83f3

def z1043 : W := mkw 0x0102a01003618c61 0x8040a80400d86318 0xf783e180e7e1ce73 0x7de0f86039f8739c

def z1044 : W := mkw 0x06d801dd01aa0f82 0x01b60077406a83e0 0xfff001ff07ee0f82 0x7ffc007fc1fb83e0

def z1045 : W := mkw 0x13fbddeef8000000 0x04fef77bbe000000 0xdbfffffff80009cf 0xf6fffffffe000273

def z1046 : W := mkw 0x0000000000000000 0x0000000000000000 0x600cfe0000113001 0xd8033f8000044c00

def z1047 : W := mkw 0x13dacdeef8000000 0x04f6b37bbe000000 0x138cee7f18000000 0x44e33b9fc6000000

def z1048 : W := mkw 0x8435329937bf7fdf 0x610d4ca64defdff7 0xec731188ffffffff 0xbb1cc4623fffffff

def z1049 : W := mkw 0x13dacdeec8000000 0x04f6b37bb2000000 0xdbffefffe0000003 0xf6fffbfff8000000

def z1050 : W := mkw 0x0182a14042618420 0x8060a85010986108 0xb783018067e1c630 0x2de0c06019f8718c

def z1051 : W := mkw 0x80253211371578dd 0x60094c844dc55e37 0x20031000ff11f9fd 0x0800c4003fc47e7f

def z1052 : W := mkw 0x8004221107311cc5 0x2001088441cc4731 0x2400000007f13fcc 0x0900000001fc4ff3

def z1053 : W := mkw 0x84042211079b1bc7 0x2101088441e6c6f1 0x20000000071f39cc 0x0800000001c7ce73

def z1054 : W := mkw 0x8004221107311ce5 0xa001088441cc4739 0x2000000007113ffc 0x0800000001c44fff

def z1055 : W := mkw 0x13dacdeec8000000 0x04f6b37bb2000000 0x9bfceff700000000 0x66ff3bfdc0000000

def z1056 : W := mkw 0x13fbddeef8408020 0x84fef77bbe102008 0xdbfffffff800c033 0xf6fffffffe00300c

def z1057 : W := mkw 0x0b6fba0006ddf000 0x02dbee8001b77c00 0x3ffcfe0007fff000 0xcfff3f8001fffc00

def z1058 : W := mkw 0x0182a15043618c61 0x8060a85410d86318 0xf783e18067e1ce71 0x7de0f86019f8739c

def z1059 : W := mkw 0x8186a35147719ce5 0xa061a8d451dc6739 0xb783018067f1fffc 0x2de0c06019fc7fff

def z1060 : W := mkw 0x0000000000000000 0x0000000000000000 0x400cfe7f00000003 0xd0033f9fc0000000

def z1061 : W := mkw 0x0182e170c3618c61 0x8060b85c30d86318 0xf783f1f0ffe1fe7f 0x7de0fc7c3ff87f9f

def z1062 : W := mkw 0x0a7d1a88349e7318 0x429f46a20d279cc6 0x087c1e00001e3000 0x821f078000078c00

def z1063 : W := mkw 0x0182e572cb618c61 0x8060b95cb2d86318 0xf783fff0ffe1ce73 0x7de0fffc3ff8739c

def z1064 : W := mkw 0x0182e170c3618c61 0x8060b85c30d86318 0xf783e1f8e7f1cff3 0xfde0f87e39fc73fc

def z1065 : W := mkw 0x0000442288000000 0x00001108a2000000 0x600cfe7f98113003 0xd8033f9fe6044c00

def z1066 : W := mkw 0x13cacd66c8000000 0x04f2b359b2000000 0x138cfe7798000001 0x44e33f9de6000000

def z1067 : W := mkw 0x13fbddeef8046018 0x44fef77bbe011806 0xdbfffffff800300f 0xf6fffffffe000c03

def z1068 : W := mkw 0x06cc015505b80c82 0x01b30055416e0320 0x1bfc007707fe0000 0xc6ff001dc1ff8000

def z1069 : W := mkw 0x13fbddeef8000000 0x04fef77bbe000000 0x1bfffe7ff8000001 0xc6ffff9ffe000000

def z1070 : W := mkw 0x06dc01dd05ba0f82 0x01b70077416e83e0 0xfffc01ffe7fe0ff2 0xffff007ff9ff83fc

def z1071 : W := mkw 0x0000442288000000 0x00001108a2000000 0x600cfe7f98100983 0xd8033f9fe6040260

def z1072 : W := mkw 0x06cc015505b80c82 0x01b30055416e0320 0xfffc007f07fe0982 0xffff001fc1ff8260

def z1073 : W := mkw 0x13fbddeef8000000 0x04fef77bbe000000 0xfffffffff8000e03 0xfffffffffe000380

def z1074 : W := mkw 0x800466338f1118c5 0x2001198ce3c44631 0x000cfe7f9f1131cd 0xc0033f9fe7c44c73

def z1075 : W := mkw 0x8004221107131bc5 0x2001088441c4c6f1 0x24000000071f3fcc 0x0900000001c7cff3

def z1076 : W := mkw 0x13cacd66c8000000 0x04f2b359b2000000 0x138fee77e0000001 0x44e3fb9df8000000

def z1077 : W := mkw 0x02f955eeb8000000 0x00be557bae000000 0xdbfffffff8000003 0xf6fffffffe000000

def z1078 : W := mkw 0x0000000000000000 0x0000000000000000 0xf7830180e7e1ce73 0x7de0c06039f8739c

def z1079 : W := mkw 0x0582e175c3618ce3 0x8160b85d70d86338 0xf783e1f7e7e1ce73 0x7de0f87df9f8739c

def z1080 : W := mkw 0x80042211071118c5 0x2001088441c44631 0xe4030180e711ffff 0x3900c06039c47fff

def z1081 : W := mkw 0x849045ffb9220fdf 0x6124117fee4883f7 0x000001fff8000ffe 0x0000007ffe0003ff

def z1082 : W := mkw 0x17fbddeef8aa0702 0x05fef77bbe2a81c0 0xfffffffff8fe0f83 0xfffffffffe3f83e0

def z1083 : W := mkw 0x037bdcaab8000000 0x00def72aae000000 0xdbfffffff8000003 0xf6fffffffe000000

def z1084 : W := mkw 0x0000442288000000 0x00001108a2000000 0x600cfe7f98010843 0xd8033f9fe6004210

def z1085 : W := mkw 0x0000442288066318 0x40001108a20198c6 0x640cfe7f981fffff 0xd9033f9fe607ffff

def z1086 : W := mkw 0x0182c170c1608c20 0x8060b05c30582308 0xf783e1f0e7e0ce33 0x7de0f87c39f8338c

def z1087 : W := mkw 0x13fbddeef8066318 0x44fef77bbe0198c6 0xdbfffffff80e0003 0xf6fffffffe038000

def z1088 : W := mkw 0x027d1088349e6318 0x409f44220d2798c6 0x087c1008181e318c 0x821f040206078c63

def z1089 : W := mkw 0x13cacd66c8000000 0x04f2b359b2000000 0x538cfe7700000001 0xd4e33f9dc0000000

def z1090 : W := mkw 0x13fbddeef8020300 0x04fef77bbe0080c0 0xfffffffff81f3fcf 0xfffffffffe07cff3

def z1091 : W := mkw 0x13dacdeef8020318 0x44f6b37bbe0080c6 0x138ceffff8000ffe 0x44e33bfffe0003ff

def z1092 : W := mkw 0x800466338f311cc5 0x2001198ce3cc4731 0x640cfe7f9ff13fcf 0xd9033f9fe7fc4ff3

def z1093 : W := mkw 0x13fbddeef8000000 0x04fef77bbe000000 0x5bfcfe7f98000003 0xd6ff3f9fe6000000

def z1094 : W := mkw 0x0b6fba0036ddf018 0x42dbee800db77c06 0xffffff80fffffe7f 0xffffffe03fffff9f

def z1095 : W := mkw 0x13cacd66c8608420 0x84f2b359b2182108 0x978feff760e0c630 0x65e3fbfdd838318c

def z1096 : W := mkw 0x86dc23dd07bb1fc7 0x21b708f741eec7f1 0xbff0018007ff3fcc 0x2ffc006001ffcff3

def z1097 : W := mkw 0x0182e170c3618c61 0x8060b85c30d86318 0xf783e1f0e7f1ffff 0x7de0f87c39fc7fff

def z1098 : W := mkw 0x13cacd66c8000000 0x04f2b359b2000000 0x538cee7780000003 0x54e33b9de0000000

def z1099 : W := mkw 0x13fbddeef8046018 0x44fef77bbe011806 0xfffffffff81ff07f 0xfffffffffe07fc1f

def z1100 : W := mkw 0x06dc01dd05ba0f82 0x01b70077416e83e0 0xfffc11ff07ff3f83 0xffff047fc1ffcfe0

def z1101 : W := mkw 0x034acc2288000000 0x00d2b308a2000000 0x538cfe7f98000003 0xd4e33f9fe6000000

def z1102 : W := mkw 0x86dc03dd05ba1f86 0x21b700f7416e87e1 0xfffc01ff07fe3f8e 0xffff007fc1ff8fe3

def z1103 : W := mkw 0x80042211071118c5 0x2001088441c44631 0x00000000070009cc 0x0000000001c00273

def z1104 : W := mkw 0x13ebdd66c8000000 0x04faf759b2000000 0x1bfcfe7700000000 0xc6ff3f9dc0000000

def z1105 : W := mkw 0x8182e573cb618ce5 0xa060b95cf2d86339 0xf78fffffffe1cfff 0xfde3fffffff873ff

def z1106 : W := mkw 0x1bfbddeef844e000 0x06fef77bbe113800 0xdbfffffff800c003 0xf6fffffffe003000

def z1107 : W := mkw 0x0182a15043618c20 0x8060a85410d86308 0xf783e1f067e1ce33 0x7de0f87c19f8738c

def z1108 : W := mkw 0x13ebdd66c8000000 0x04faf759b2000000 0x9bffee7700000000 0x66fffb9dc0000000

def z1109 : W := mkw 0x02d845ee88000000 0x00b6117ba2000000 0xdbfcefff00000002 0xf6ff3bffc0000000

def z1110 : W := mkw 0x13fbddeef8046000 0x04fef77bbe011800 0xdbfffffff81e3003 0xf6fffffffe078c00

def z1111 : W := mkw 0x13ebdd66f8000000 0x04faf759be000000 0xdbfffe77f8000001 0xf6ffff9dfe000000

def z1112 : W := mkw 0x10004422f8000000 0x04001108be000000 0x400cfe7ff8000003 0xd0033f9ffe000000

def z1113 : W := mkw 0x0b6fba0036ddf018 0x42dbee800db77c06 0xfffffe08fffff9ff 0xffffff823ffffe7f

def z1114 : W := mkw 0x8182e772cb619c65 0xa060b9dcb2d86719 0xf783fff8fff1ffff 0xfde0fffe3ffc7fff

def z1115 : W := mkw 0x12795caeb8000000 0x049e572bae000000 0xc87ffffff8000003 0xf21ffffffe000000

def z1116 : W := mkw 0x0c04221107fb9f82 0x0301088441fee7e0 0x2400000007fe0f80 0x0900000001ff83e0

def z1117 : W := mkw 0x034acc2288000000 0x00d2b308a2000000 0x138cee7700000000 0x44e33b9dc0000000

def z1118 : W := mkw 0x06dc01dd05ba0f82 0x01b70077416e83e0 0x9ffc01ff07ee0f82 0x67ff007fc1fb83e0

def z1119 : W := mkw 0x036bdc2288046000 0x00daf708a2011800 0xfffffe7f981ff9cf 0xffffff9fe607fe73

def z1120 : W := mkw 0x13fbddeef8066318 0x44fef77bbe0198c6 0xdbfffffff81e3fff 0xf6fffffffe078fff

def z1121 : W := mkw 0x0b6fba0006d99000 0x02dbee8001b66400 0xfffffe0007fe0001 0xffffff8001ff8000

def z1122 : W := mkw 0x06dc01dd05ba0f82 0x01b70077416e83e0 0xffff01ff07ffcf83 0xffffc07fc1fff3e0

def z1123 : W := mkw 0x0031108830066318 0x400c44220c0198c6 0xec7f11fff81fffff 0xfb1fc47ffe07ffff

def z1124 : W := mkw 0x8b6fba0106ddf084 0x22dbee8041b77c21 0xfffffe0007fff18d 0xffffff8001fffc63

def z1125 : W := mkw 0x06dc01dd05ba0f82 0x01b70077416e83e0 0xfffc01ff9ffe0fce 0xffff007fe7ff83f3

def z1126 : W := mkw 0x0b6fba0106ddf080 0x02dbee8041b77c20 0xfffffe0f07fff181 0xffffff83c1fffc60

def z1127 : W := mkw 0x0000442288000000 0x00001108a2000000 0x0000fe009801304d 0x00003f8026004c13

def z1128 : W := mkw 0x0031108830066318 0x400c44220c0198c6 0xec7fff88f81fffff 0xfb1fffe23e07ffff

def z1129 : W := mkw 0x06dc01dd05ba0f82 0x01b70077416e83e0 0xffff01ff67fecfb2 0xffffc07fd9ffb3ec

def z1130 : W := mkw 0x17fbddeef8a80402 0x05fef77bbe2a0100 0xdbfffffff8e00003 0xf6fffffffe380000

def z1131 : W := mkw 0x136bdc22f8000000 0x04daf708be000000 0xdbfffe7ff8000003 0xf6ffff9ffe000000

def z1132 : W := mkw 0x06dc01dd05ba0f82 0x01b70077416e83e0 0x9ff0018007ee0600 0x27fc006001fb8180

def z1133 : W := mkw 0x8835329937dffbdd 0x620d4ca64df7fef7 0xec731188ffffffff 0xbb1cc4623fffffff

def z1134 : W := mkw 0x13cacd66f8000000 0x04f2b359be000000 0x138cee77f8000000 0x44e33b9dfe000000

def z1135 : W := mkw 0x800466338f1118c5 0x2001198ce3c44631 0x200000009f1139cc 0x0800000027c44e73

def z1136 : W := mkw 0x13ebdd66f8000000 0x04faf759be000000 0xd38ffff7f8000003 0x74e3fffdfe000000

def z1137 : W := mkw 0x0b6fba0006ddf000 0x02dbee8001b77c00 0x9ffffe0007eff001 0x67ffff8001fbfc00

def z1138 : W := mkw 0x024c220006991000 0x0093088001a64400 0xfffcee0007fe0000 0xffff3b8001ff8000

def z1139 : W := mkw 0x13fbddeef8000000 0x04fef77bbe000000 0xdbfffffff801304f 0xf6fffffffe004c13

def z1140 : W := mkw 0x149045ffc9220f82 0x0524117ff24883e0 0x000001ff00000f82 0x0000007fc00003e0

def z1141 : W := mkw 0x0b6fba0006ddf000 0x02dbee8001b77c00 0xfffcfe0007fe3000 0xffff3f8001ff8c00

def z1142 : W := mkw 0x13fb9dce38000000 0x04fee7738e000000 0xdbffffff18000003 0xf6ffffffc6000000

def z1143 : W := mkw 0x0010008800020300 0x00040022000080c0 0xec731188f81fffff 0xbb1cc4623e07ffff

def z1144 : W := mkw 0x800426130f111884 0x20010984c3c44621 0x600cfe7f1f11398f 0xd8033f9fc7c44e63

def z1145 : W := mkw 0x800466338f1118c5 0x2001198ce3c44631 0x600cffffff113fff 0xd8033fffffc44fff

def z1146 : W := mkw 0x0000442288000000 0x00001108a2000000 0x000cfe7f18000000 0xc0033f9fc6000000

def z1147 : W := mkw 0x80042211071118c5 0x2001088441c44631 0x2000000007100980 0x0800000001c40260

def z1148 : W := mkw 0x13fbddeef8020318 0x44fef77bbe0080c6 0xdbfffffff8000633 0xf6fffffffe00018c

def z1149 : W := mkw 0x0248442288000000 0x00921108a2000000 0xdbfcfe7f98000003 0xf6ff3f9fe6000000

def z1150 : W := mkw 0x0000442288000000 0x00001108a2000000 0x400cee7f00000002 0xd0033b9fc0000000

def z1151 : W := mkw 0x025c0099059a0b80 0x00970026416682e0 0xfffc01ff07fe0f82 0xffff007fc1ff83e0

def z1152 : W := mkw 0x03dac5eec8000000 0x00f6b17bb2000000 0xdbfffffff8000003 0xf6fffffffe000000

def z1153 : W := mkw 0x13fb99cc70000000 0x04fee6731c000000 0xdbffffff60000003 0xf6ffffffd8000000

def z1154 : W := mkw 0x809045fbf9220ffd 0xe024117efe4883ff 0x000001fff8000ffe 0x0000007ffe0003ff

def z1155 : W := mkw 0x0000402080000000 0x0000100820000000 0x6000e07080010843 0x5800381c20004210

def z1156 : W := mkw 0x06dc01dd05ba0f82 0x01b70077416e83e0 0xfffc01ff07ffcff2 0xffff007fc1fff3fc

def z1157 : W := mkw 0x0182815041608c20 0x8060a05410582308 0x978301f067e0c630 0x65e0c07c19f8318c

def z1158 : W := mkw 0x8182e370c3619c65 0xa060b8dc30d86719 0xf783e1f0e7e1fe7f 0x7de0f87c39f87f9f

def z1159 : W := mkw 0x17fbddeef88a0302 0x05fef77bbe2280c0 0xdbfffffff80e0003 0xf6fffffffe038000

def z1160 : W := mkw 0x80042211075198e5 0xa001088441d46639 0x200000000711f9fc 0x0800000001c47e7f

def z1161 : W := mkw 0x80042211075198c5 0x2001088441d46631 0x2400000007f1f9cc 0x0900000001fc7e73

def z1162 : W := mkw 0x0b6fba0006ddf000 0x02dbee8001b77c00 0x9ffffe0007fef000 0xe7ffff8001ffbc00

def z1163 : W := mkw 0x0b6fba0006ddf018 0x42dbee8001b77c06 0xfffffe0007fff07d 0xffffff8001fffc1f

def z1164 : W := mkw 0x06d845ee88aa0702 0x01b6117ba22a81c0 0xdffcffff98ee0603 0xf7ff3fffe63b8180

def z1165 : W := mkw 0x800466338f1118c5 0x2001198ce3c44631 0x600ffe7fff11f9ff 0xd803ff9fffc47e7f

def z1166 : W := mkw 0x13fbddeef8000000 0x04fef77bbe000000 0xfbfffffff8100983 0xfefffffffe040260

def z1167 : W := mkw 0x0021542288046000 0x00085508a2011800 0xec7ffe7f981ff003 0xfb1fff9fe607fc00

def z1168 : W := mkw 0x1bfbddeef8ece420 0x86fef77bbe3b3908 0xdffffffff8eec633 0xf7fffffffe3bb18c

def z1169 : W := mkw 0x0b6fba0036ddf018 0x42dbee800db77c06 0xfffffe001ffff00d 0xffffff8007fffc03

def z1170 : W := mkw 0x13dacdeec8020300 0x04f6b37bb20080c0 0xfffcefff001e0f82 0xffff3bffc00783e0

def z1171 : W := mkw 0x0080617083210c41 0x0020185c20c84310 0xf783e1f0e7e1ce73 0x7de0f87c39f8739c

def z1172 : W := mkw 0x8923fe22ba45f05d 0x6248ff88ae917c17 0x0003fe00f801f07d 0x0000ff803e007c1f

def z1173 : W := mkw 0x0c35329937ffff9a 0x430d4ca64dffffe6 0xec731188ffffffff 0xbb1cc4623fffffff

def z1174 : W := mkw 0x13fbddeef8046000 0x04fef77bbe011800 0xdffffffff80ec003 0xf7fffffffe03b000

def z1175 : W := mkw 0x02c8456688000000 0x00b21159a2000000 0x538cfe7f98000003 0xd4e33f9fe6000000

def z1176 : W := mkw 0x13fbddeef8000000 0x04fef77bbe000000 0x138ffffff8000003 0x44e3fffffe000000

def z1177 : W := mkw 0x13fbddeef8066318 0x44fef77bbe0198c6 0xdffffffff81ef7bf 0xf7fffffffe07bdef

def z1178 : W := mkw 0x0c04221107f99c82 0x0301088441fe6720 0x0000000007e00000 0x0000000001f80000

def z1179 : W := mkw 0x1133dcaaf8000000 0x044cf72abe000000 0xc87ffffff8000003 0xf21ffffffe000000

def z1180 : W := mkw 0x13fbddeef8066318 0x44fef77bbe0198c6 0xdffffffff80ecfff 0xf7fffffffe03b3ff

def z1181 : W := mkw 0x13fb99cc70066318 0x44fee6731c0198c6 0x9bf30180600e0000 0x26fcc06018038000

def z1182 : W := mkw 0x067d108d349e639a 0x419f44234d2798e6 0x087c000f001e0180 0x821f0003c0078060

def z1183 : W := mkw 0x109045eef8020318 0x4424117bbe0080c6 0x600cfffff8113fff 0xd8033ffffe044fff

def z1184 : W := mkw 0x13fbddeef8000000 0x04fef77bbe000000 0x1bfcee7700000000 0x46ff3b9dc0000000

def z1185 : W := mkw 0x13fbddeef8066318 0x44fef77bbe0198c6 0xfffffffff81ff18f 0xfffffffffe07fc63

def z1186 : W := mkw 0x0182e170c3618c61 0x8060b85c30d86318 0xb783e180e7e1ce71 0x2de0f86039f8739c

def z1187 : W := mkw 0x06dc01dd05ba0fe3 0x81b70077416e83f8 0xfffc01ff07fe0ff2 0xffff007fc1ff83fc

def z1188 : W := mkw 0x13fbddeef8000000 0x04fef77bbe000000 0xffffffffffe00003 0xfffffffffff80000

def z1189 : W := mkw 0x0b6bdc2288cce000 0x02daf708a2333800 0xdffffe7f98eec003 0xf7ffff9fe63bb000

def z1190 : W := mkw 0x06dc01dd05ba0f9a 0x41b70077416e83e6 0xfffc01ff07fe0ffe 0xffff007fc1ff83ff

def z1191 : W := mkw 0x02c8456688000000 0x00b21159a2000000 0x138cee7700000000 0x44e33b9dc0000000

def z1192 : W := mkw 0x13fbddeef8000000 0x04fef77bbe000000 0xdbfffffff8000e73 0xf6fffffffe00039c

def z1193 : W := mkw 0x80046633cf1118e5 0xa001198cf3c44639 0x600cfe7fff1139ff 0xd8033f9fffc44e7f

def z1194 : W := mkw 0x06dc01cd049a0382 0x01b70073412680e0 0xfffc01ff07fe0182 0xffff007fc1ff8060

def z1195 : W := mkw 0x8035329937177bdd 0x600d4ca64dc5def7 0x287010081f1f39cc 0x8a1c040207c7ce73

def z1196 : W := mkw 0x0b6fba0006ddf000 0x02dbee8001b77c00 0xfffffe0807fff983 0xffffff8201fffe60

def z1197 : W := mkw 0x8004221107177bdd 0x6001088441c5def7 0x20000000071f39cc 0x0800000001c7ce73

def z1198 : W := mkw 0x17fbddeef8ae671a 0x45fef77bbe2b99c6 0xdffffffff8eec633 0xf7fffffffe3bb18c

def z1199 : W := mkw 0x8404221107fb9fe7 0xa101088441fee7f9 0x2400000007fffffc 0x0900000001ffffff

def z1200 : W := mkw 0x0a6d3a00069d7000 0x029b4e8001a75c00 0xfffcfe0007ff3001 0xffff3f8001ffcc00

def z1201 : W := mkw 0x0b6fba0006ddf000 0x02dbee8001b77c00 0x7bfcfe0007ff3001 0xdeff3f8001ffcc00

def z1202 : W := mkw 0x800466338f1118c5 0x2001198ce3c44631 0x600cfe7f1f11318d 0xd8033f9fc7c44c63

def z1203 : W := mkw 0x8182e573cb618ce5 0xa060b95cf2d86339 0xf783f1fffff1ffff 0xfde0fc7ffffc7fff

def z1204 : W := mkw 0x800466338f1118c5 0x2001198ce3c44631 0xe00fffffff1139cf 0xf803ffffffc44e73

def z1205 : W := mkw 0x80042211071118c5 0x2001088441c44631 0x000000000701304c 0x0000000001c04c13

def z1206 : W := mkw 0x06dc01dd05ba0f82 0x01b70077416e83e0 0xbff001ff07fe0f82 0x2ffc007fc1ff83e0

def z1207 : W := mkw 0x88042211079d78c5 0x2201088441e75e31 0x20000000071f39cc 0x0800000001c7ce73

def z1208 : W := mkw 0x137bdcaef8000000 0x04def72bbe000000 0x487ffe7ff8000003 0xd21fff9ffe000000

def z1209 : W := mkw 0x025844ae88000000 0x0096112ba2000000 0x487cfe7f98000003 0xd21f3f9fe6000000

def z1210 : W := mkw 0x0b4eaa0006ddf000 0x02d3aa8001b77c00 0xfffcee0007fff000 0xffff3b8001fffc00

def z1211 : W := mkw 0x06dc01dd05ba0f82 0x01b70077416e83e0 0xfffc01f707fe0600 0xffff007dc1ff8180

def z1212 : W := mkw 0x13fbddeef8066318 0x44fef77bbe0198c6 0xfbfffffff81f39cf 0xfefffffffe07ce73

def z1213 : W := mkw 0x0182e170c3618c61 0x8060b85c30d86318 0x1383e1f0e7e1ce73 0x44e0f87c39f8739c

def z1214 : W := mkw 0x0b6fba0036ddf018 0x42dbee800db77c06 0xfffffe0067fff031 0xffffff8019fffc0c

def z1215 : W := mkw 0x0b6fba0006ddf000 0x02dbee8001b77c00 0x1bfffe0007fff001 0xc6ffff8001fffc00

def z1216 : W := mkw 0x06cc015505b80c82 0x01b30055416e0320 0x9ffc007707ee0000 0x67ff001dc1fb8000

def z1217 : W := mkw 0x0b6fba0006ddf000 0x02dbee8001b77c00 0xffffee0007efc001 0x7ffffb8001fbf000

def z1218 : W := mkw 0x02dc01dc05b80c00 0x00b70077016e0300 0xfffc01ff07fe0e02 0xffff007fc1ff8380

def z1219 : W := mkw 0x03fb99cc30066318 0x40fee6730c0198c6 0xfffffffff81fffff 0xfffffffffe07ffff

def z1220 : W := mkw 0x036bdc2288000000 0x00daf708a2000000 0xdbfffe7700000001 0xf6ffff9dc0000000

def z1221 : W := mkw 0x800466238e111084 0x20011988e3844421 0x600cfe7f9f11318f 0xd8033f9fe7c44c63

def z1222 : W := mkw 0x8414229907bb1fc7 0x210508a641eec7f1 0xec7011889fff3fcf 0xbb1c046227ffcff3

def z1223 : W := mkw 0x13fbddeef8880000 0x04fef77bbe220000 0xdffffffff8ee0003 0xf7fffffffe3b8000

def z1224 : W := mkw 0x13fbddeef8066318 0x44fef77bbe0198c6 0xfffffffff81ecfb3 0xfffffffffe07b3ec

def z1225 : W := mkw 0x93fbddeef8000045 0x24fef77bbe000011 0xdbfffffff800004f 0xf6fffffffe000013

def z1226 : W := mkw 0x0123dc2288000000 0x0048f708a2000000 0x400ffe7f98000003 0xd003ff9fe6000000

def z1227 : W := mkw 0x06dc01dd45ba0fa2 0x81b70077516e83e8 0xfffc01ff67fe0fb2 0xffff007fd9ff83ec

def z1228 : W := mkw 0x16dc01dd75ba0f82 0x05b700775d6e83e0 0xfffc01ff67fe0f82 0xffff007fd9ff83e0

def z1229 : W := mkw 0x13fbddeef8000000 0x04fef77bbe000000 0xdffffffff800c633 0xf7fffffffe00318c

def z1230 : W := mkw 0x0b6fba0006ddf000 0x02dbee8001b77c00 0xfffffe0087fff843 0xffffff8021fffe10

def z1231 : W := mkw 0x13dacdeec8000000 0x04f6b37bb2000000 0x1bfcee7f00000000 0xc6ff3b9fc0000000

def z1232 : W := mkw 0x12795caeb8066318 0x449e572bae0198c6 0x687cfe7f981f39cf 0xda1f3f9fe607ce73

def z1233 : W := mkw 0x8004221107719ce5 0xa001088441dc6739 0x0000000007e00000 0x0000000001f80000

def z1234 : W := mkw 0x8035329937177bdd 0x600d4ca64dc5def7 0xac730180671ffffc 0x2b1cc06019c7ffff

def z1235 : W := mkw 0x0127b2000655f000 0x0049ec8001957c00 0xfffffe0007fff001 0xffffff8001fffc00

def z1236 : W := mkw 0x8182e772cb619c65 0xa060b9dcb2d86719 0xf783eff0e7e1ce73 0x7de0fbfc39f8739c

def z1237 : W := mkw 0x1bfbddeef8c88000 0x06fef77bbe322000 0xdbfffffff8e00003 0xf6fffffffe380000

def z1238 : W := mkw 0x800466338f5198e5 0xa001198ce3d46639 0x600cfe7f9f11f9ff 0xd8033f9fe7c47e7f

def z1239 : W := mkw 0x8bceef73cff99ce5 0xa2f3bbdcf3fe6739 0x138cee7707e00000 0x44e33b9dc1f80000

def z1240 : W := mkw 0x0000442288000000 0x00001108a2000000 0xc00ffffff8000003 0xf003fffffe000000

def z1241 : W := mkw 0x0f6fba0506ddf082 0x03dbee8141b77c20 0xfffffe0707fff001 0xffffff81c1fffc00

def z1242 : W := mkw 0x8123f622fa45f07d 0xe048fd88be917c1f 0x0003fe00f801f07d 0x0000ff803e007c1f

def z1243 : W := mkw 0x87cee777cff99ce7 0xa1f3b9ddf3fe6739 0x138cee7707e00000 0x44e33b9dc1f80000

def z1244 : W := mkw 0x06dc01dd05ba0f82 0x01b70077416e83e0 0xfffc11ff1ffe3f8e 0xffff047fc7ff8fe3

def z1245 : W := mkw 0x0182e170c3618c61 0x8060b85c30d86318 0xf783e1f8ffe1cfff 0x7de0f87e3ff873ff

def z1246 : W := mkw 0x0b6fba0006ddf000 0x02dbee8001b77c00 0xffffff8007fffe03 0xffffffe001ffff80

def z1247 : W := mkw 0x01b3d5eaf8000000 0x006cf57abe000000 0xdbfffffff8000003 0xf6fffffffe000000

def z1248 : W := mkw 0x8c04221107ffffc7 0x2301088441fffff1 0x2400000007ffffcc 0x0900000001fffff3

def z1249 : W := mkw 0x024c001105980880 0x0093000441660220 0xfffc007707fe0000 0xffff001dc1ff8000

def z1250 : W := mkw 0x80042211071118c5 0x2001088441c44631 0x2000000007113000 0x0800000001c44c00

def z1251 : W := mkw 0x13fbddeef8608420 0x84fef77bbe182108 0xdbfffffff8e00003 0xf6fffffffe380000

def z1252 : W := mkw 0x001044aab8000000 0x0004112aae000000 0x400cfffff8000003 0xd0033ffffe000000

def z1253 : W := mkw 0x0000442288000000 0x00001108a2000000 0x400cfe7700000001 0xd0033f9dc0000000

def z1254 : W := mkw 0x13fbddeef8066318 0x44fef77bbe0198c6 0x1bfcfe7f181e318c 0xc6ff3f9fc6078c63

def z1255 : W := mkw 0x0182a14042618420 0x8060a85010986108 0x9783e18067e0c630 0x65e0f86019f8318c

def z1256 : W := mkw 0x003154aab8000000 0x000c552aae000000 0x487cfe7f98000003 0xd21f3f9fe6000000

def z1257 : W := mkw 0x80042211071118c5 0x2001088441c44631 0x2000000007010840 0x0800000001c04210

def z1258 : W := mkw 0x06dc01dd05ba0f82 0x01b70077416e83e0 0xffff11ffffffffff 0xffffc47fffffffff

def z1259 : W := mkw 0x06dc01dd35ba0f82 0x01b700774d6e83e0 0xfffc01fffffe0f82 0xffff007fffff83e0

def z1260 : W := mkw 0x8004221107131bdd 0x6001088441c4c6f7 0x2000000007113ffc 0x0800000001c44fff

def z1261 : W := mkw 0x800466238e1110c5 0x20011988e3844431 0x400cfe7f981131cf 0xd0033f9fe6044c73

def z1262 : W := mkw 0x0b4eaa0006d99000 0x02d3aa8001b66400 0xffffee0007ffc001 0xfffffb8001fff000

def z1263 : W := mkw 0x13fbddeef8000000 0x04fef77bbe000000 0xfbfffffff8113003 0xfefffffffe044c00

def z1264 : W := mkw 0x06dc01dd05ba0f82 0x01b70077416e83e0 0xfffcffff07fe0f83 0xffff3fffc1ff83e0

def z1265 : W := mkw 0x13fbddeef8020300 0x04fef77bbe0080c0 0xdbfffffff8000f83 0xf6fffffffe0003e0

def z1266 : W := mkw 0x13cacd66c8000000 0x04f2b359b2000000 0xd38ffffff8000003 0xf4e3fffffe000000

def z1267 : W := mkw 0x13fbddeef8000000 0x04fef77bbe000000 0xfbfffffff8010843 0xfefffffffe004210

def z1268 : W := mkw 0x12f95deef8000000 0x04be577bbe000000 0x487cfffff8000003 0xd21f3ffffe000000

def z1269 : W := mkw 0x13fbddeef8020318 0x44fef77bbe0080c6 0xfbfffffff8113fff 0xfefffffffe044fff

def z1270 : W := mkw 0x065c009d059a0b82 0x01970027416682e0 0xfffc007f07fe0982 0xffff001fc1ff8260

def z1271 : W := mkw 0x0923fe228a45f000 0x0248ff88a2917c00 0x0003fe009801f001 0x0000ff8026007c00

def z1272 : W := mkw 0x13fbddeef8066318 0x44fef77bbe0198c6 0x9fffeff7600ec630 0x67fffbfdd803b18c

def z1273 : W := mkw 0x80042211071578c5 0x2001088441c55e31 0x24000000071ff9cc 0x0900000001c7fe73

def z1274 : W := mkw 0x800066338b0118c5 0x2000198ce2c04631 0x400cfe7f980139cf 0xd0033f9fe6004e73

def z1275 : W := mkw 0x13fbddeef8066318 0x44fef77bbe0198c6 0xdffffffff80ff67f 0xf7fffffffe03fd9f

def z1276 : W := mkw 0x1123dc22f8000000 0x0448f708be000000 0x000ffe77f8000001 0x4003ff9dfe000000

def z1277 : W := mkw 0x13cacd66c8000000 0x04f2b359b2000000 0xdbfcee7700000000 0xf6ff3b9dc0000000

def z1278 : W := mkw 0x06dc01dd05ba0f82 0x01b70077416e83e0 0xfffc007f07fe0180 0xffff001fc1ff8060

def z1279 : W := mkw 0x00804170c1200c61 0x8020105c30480318 0xf78301f0e7e1ce73 0x7de0c07c39f8739c

def z1280 : W := mkw 0x12d845eef8000000 0x04b6117bbe000000 0xdbfcfffff8000003 0xf6ff3ffffe000000

def z1281 : W := mkw 0x8b6fba1107ddf8c5 0x22dbee8441f77e31 0xbff3000007fff9cc 0x2ffcc00001fffe73

def z1282 : W := mkw 0x13fbddeef8046000 0x04fef77bbe011800 0xfffffffff81ff9cf 0xfffffffffe07fe73

def z1283 : W := mkw 0x8404221107331fc7 0x2101088441ccc7f1 0x2000000007113fcc 0x0800000001c44ff3

def z1284 : W := mkw 0x1b6fba0076ddf000 0x06dbee801db77c00 0xfffffe0067fff001 0xffffff8019fffc00

def z1285 : W := mkw 0x800466338f1118c5 0x2001198ce3c44631 0x000cfe7f9f1039ce 0xc0033f9fe7c40e73

def z1286 : W := mkw 0x0000442288000000 0x00001108a2000000 0x400cfe7f9801304f 0xd0033f9fe6004c13

def z1287 : W := mkw 0x0b4eaa0006d99000 0x02d3aa8001b66400 0x9ffcee0007ee0000 0x67ff3b8001fb8000

def z1288 : W := mkw 0x13fbddeef8066318 0x44fef77bbe0198c6 0xdbfffffff81ff1ff 0xf6fffffffe07fc7f

def z1289 : W := mkw 0x11a3dd62f8000000 0x0468f758be000000 0xd38ffffff8000003 0xf4e3fffffe000000

def z1290 : W := mkw 0x12484c2688000000 0x04921309a2000000 0x400cfe7f98000003 0xd0033f9fe6000000

def z1291 : W := mkw 0x001044aa88000000 0x0004112aa2000000 0xc87cffff98000003 0xf21f3fffe6000000

def z1292 : W := mkw 0x0102e03083418841 0x0040b80c20d06210 0xf783e1f0e7e1ce73 0x7de0f87c39f8739c

def z1293 : W := mkw 0x0000442288000000 0x00001108a2000000 0x400cfe7f980009cf 0xd0033f9fe6000273

def z1294 : W := mkw 0x13fbddeef8020300 0x04fef77bbe0080c0 0xfffffffff81fcff3 0xfffffffffe07f3fc

def z1295 : W := mkw 0x8182e773cb619ce5 0xa060b9dcf2d86739 0xf783ffffffe1ffff 0x7de0fffffff87fff

def z1296 : W := mkw 0x8014229907131bc5 0x200508a641c4c6f1 0xec700188071f3fce 0xbb1c006201c7cff3

def z1297 : W := mkw 0x00215422b8000000 0x00085508ae000000 0x400ffe7ff8000003 0xd003ff9ffe000000

def z1298 : W := mkw 0x0182c170c1608c61 0x8060b05c30582318 0xf78301f0e7e0ce72 0x7de0c07c39f8339c

def z1299 : W := mkw 0x0b6fba0006ddf000 0x02dbee8001b77c00 0xdbfffe0007fe3001 0xf6ffff8001ff8c00

def z1300 : W := mkw 0x1123dc22f8046018 0x4448f708be011806 0x600ffe7ff811f9ff 0xd803ff9ffe047e7f

def z1301 : W := mkw 0x064c001105ba0f82 0x01930004416e83e0 0xfffc007f07fe0f82 0xffff001fc1ff83e0

def z1302 : W := mkw 0x13fbddeec8000000 0x04fef77bb2000000 0xdbffffff00000003 0xf6ffffffc0000000

def z1303 : W := mkw 0x03fbddee88000000 0x00fef77ba2000000 0xdbffffff98000003 0xf6ffffffe6000000

def z1304 : W := mkw 0x06dc01dd35ba0f9a 0x41b700774d6e83e6 0xfffc01ff67fe0fb2 0xffff007fd9ff83ec

def z1305 : W := mkw 0x0b6fba0006ddf000 0x02dbee8001b77c00 0xffffee0007fec000 0xfffffb8001ffb000

def z1306 : W := mkw 0x13fbddeef8000000 0x04fef77bbe000000 0xfffffffff801c003 0xfffffffffe007000

def z1307 : W := mkw 0x10b155eef8000000 0x042c557bbe000000 0xc87ffffff8000003 0xf21ffffffe000000

def z1308 : W := mkw 0x0804221107ddf880 0x0201088441f77e20 0x2400000007fff980 0x0900000001fffe60

def z1309 : W := mkw 0x034ea20006d99000 0x00d3a88001b66400 0xfffffe0007fff001 0xffffff8001fffc00

def z1310 : W := mkw 0x0080015001200c00 0x0020005400480300 0xf78301f067e0ce32 0x7de0c07c19f8338c

def z1311 : W := mkw 0x13fbddeef8066318 0x44fef77bbe0198c6 0xfffffffff81ff633 0xfffffffffe07fd8c

def z1312 : W := mkw 0x8182e573cb618ce5 0xa060b95cf2d86339 0xf783e1f7e7e1ce73 0x7de0f87df9f8739c

def z1313 : W := mkw 0x0b6fba0006ddf000 0x02dbee8001b77c00 0xfffffe0007fffe71 0xffffff8001ffff9c

def z1314 : W := mkw 0x13fbddeef8020318 0x44fef77bbe0080c6 0xfffffffff801cfff 0xfffffffffe0073ff

def z1315 : W := mkw 0x0e7d1a8d349e739a 0x439f46a34d279ce6 0x087c1e0f181e318c 0x821f0783c6078c63

def z1316 : W := mkw 0x13fbddeef8066318 0x44fef77bbe0198c6 0xfffffffff80fce73 0xfffffffffe03f39c

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z0,z2,z3,z4,z8,z6]),(1,[z0,z2,z3,z4,z9,z6]),(0,[z0,z2,z3,z4,z5,z6,z10]),(0,[z11,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z12,z5,z6]),(0,[z0,z2,z13,z3,z4,z14,z6])],[(0,[z0,z2,z3,z15,z4,z8,z6]),(0,[z0,z16,z2,z3,z4,z5,z6]),(0,[z0,z2,z17,z3,z4,z5,z6])],[(0,[z0,z2,z18,z3,z4,z5,z6]),(0,[z0,z2,z3,z19,z4,z5,z6]),(0,[z20,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z21])],[(0,[z22,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z23,z24,z6]),(0,[z0,z2,z3,z25,z4,z26,z6]),(0,[z0,z27,z3,z4,z5,z6,z28]),(0,[z29,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z30]),(1,[z0,z31,z3,z4,z5,z6])],[(0,[z32,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z33,z6]),(0,[z0,z2,z3,z4,z34,z5,z6]),(0,[z0,z2,z3,z4,z5,z35,z6]),(0,[z0,z2,z3,z36,z4,z5,z6]),(0,[z37,z38,z0,z2,z3,z4,z6])],[(1,[z39,z2,z3,z15,z5,z6]),(0,[z0,z40,z2,z3,z4,z24,z6]),(0,[z41,z0,z2,z3,z4,z8,z6]),(0,[z0,z42,z2,z3,z4,z5,z6]),(1,[z0,z43,z3,z4,z5,z6]),(0,[z44,z0,z2,z3,z4,z8,z6])],[(0,[z0,z2,z3,z45,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z46])],[(0,[z0,z47,z2,z3,z4,z5,z6]),(1,[z48,z2,z3,z4,z5,z49]),(1,[z0,z50,z2,z3,z4,z6]),(0,[z0,z2,z51,z3,z4,z8,z6])]],
   [[(0,[z0,z2,z3,z4,z8,z6,z49]),(0,[z0,z3,z52,z4,z5,z6,z28]),(0,[z0,z2,z25,z4,z5,z53,z6]),(0,[z0,z2,z54,z4,z55,z5,z6]),(0,[z0,z2,z3,z56,z4,z5,z6])],[(1,[z0,z2,z3,z4,z24,z6]),(0,[z29,z0,z2,z3,z4,z57,z6]),(0,[z58,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z59,z3,z4,z8,z6])],[(0,[z0,z2,z3,z4,z5,z6,z60]),(0,[z0,z61,z62,z3,z4,z5,z6]),(0,[z0,z63,z2,z3,z64,z5,z6]),(0,[z0,z2,z3,z4,z65,z5,z6])],[(0,[z66,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z67,z4,z5,z6]),(0,[z48,z0,z2,z3,z4,z68,z6]),(0,[z69,z0,z2,z3,z4,z70,z6]),(0,[z0,z71,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z72,z5,z8])],[(1,[z0,z2,z3,z4,z73,z6]),(0,[z0,z2,z3,z74,z4,z5,z6]),(1,[z0,z2,z75,z4,z5,z6]),(0,[z0,z2,z76,z3,z4,z5,z6]),(0,[z77,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z78,z6])],[(0,[z0,z40,z2,z3,z4,z26,z6]),(1,[z0,z79,z2,z3,z4,z6]),(0,[z80,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z15,z64,z5,z6]),(1,[z0,z81,z3,z4,z5,z6]),(1,[z0,z2,z54,z4,z55,z6]),(0,[z0,z2,z3,z4,z82,z8,z6]),(0,[z0,z2,z3,z4,z5,z6,z83])],[(0,[z84,z0,z2,z3,z4,z73,z6]),(1,[z0,z85,z3,z4,z5,z6]),(0,[z0,z2,z3,z86,z4,z5,z6]),(0,[z0,z2,z3,z87,z4,z5,z6]),(0,[z38,z38,z0,z2,z3,z4,z6]),(1,[z38,z0,z2,z3,z4,z8])]],
   [[(0,[z88,z0,z2,z3,z4,z5,z6]),(0,[z89,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z90,z5,z6]),(0,[z0,z2,z25,z4,z91,z5,z6])],[(0,[z7,z0,z2,z3,z92,z5,z6]),(0,[z0,z2,z93,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z26,z6]),(0,[z0,z2,z3,z25,z4,z5,z6])],[(0,[z38,z94,z0,z2,z3,z4,z6]),(1,[z0,z2,z3,z4,z95,z6]),(0,[z48,z0,z2,z3,z4,z5,z49]),(0,[z96,z0,z2,z3,z4,z5,z6]),(0,[z97,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z98]),(0,[z0,z2,z99,z3,z4,z8,z6]),(0,[z0,z2,z100,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z101])],[(0,[z0,z0,z2,z3,z4,z24,z6])],[(0,[z84,z0,z2,z3,z4,z26,z6]),(0,[z0,z2,z102,z3,z4,z24,z6]),(0,[z38,z69,z0,z2,z3,z4,z6])],[(0,[z103,z0,z2,z3,z4,z104,z6]),(0,[z0,z2,z27,z105,z4,z5,z6]),(0,[z0,z2,z54,z3,z4,z26,z6]),(0,[z38,z106,z0,z2,z3,z4,z6])],[(0,[z0,z2,z3,z107,z4,z5,z6]),(1,[z0,z2,z3,z108,z5,z6]),(0,[z0,z2,z3,z4,z109,z5,z6]),(0,[z0,z2,z3,z4,z110,z6,z28]),(0,[z0,z2,z111,z3,z4,z5,z6])],[(0,[z0,z2,z4,z5,z112,z14,z6])]],
   [[(0,[z0,z113,z2,z3,z4,z5,z6]),(0,[z0,z114,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z115,z4,z5,z6]),(0,[z0,z2,z3,z4,z116,z5,z6])],[(0,[z117,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z118,z3,z4,z5,z6]),(0,[z0,z2,z119,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z120]),(1,[z38,z0,z2,z3,z4,z121]),(0,[z0,z2,z3,z4,z5,z14,z6]),(0,[z0,z2,z3,z4,z122,z5,z6])],[(0,[z103,z0,z123,z3,z4,z5,z6]),(0,[z124,z0,z2,z3,z4,z9,z6]),(0,[z0,z2,z3,z4,z24,z24,z6]),(0,[z0,z0,z2,z3,z4,z26,z6]),(0,[z0,z40,z2,z3,z4,z5,z6]),(0,[z38,z0,z2,z3,z4,z64,z6]),(0,[z0,z2,z3,z4,z125,z5,z6]),(0,[z0,z61,z2,z3,z4,z8,z6]),(0,[z0,z2,z51,z3,z91,z5,z6]),(0,[z0,z2,z126,z4,z5,z6,z127])],[(1,[z0,z2,z3,z4,z5,z60]),(0,[z0,z2,z3,z4,z5,z6,z128]),(0,[z0,z2,z3,z4,z129,z26,z6]),(0,[z130,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z131,z3,z4,z5,z6]),(0,[z132,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z133,z6])],[(0,[z0,z134,z2,z3,z4,z5,z6]),(0,[z0,z2,z135,z3,z4,z5,z6]),(0,[z0,z2,z3,z136,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z137]),(0,[z0,z2,z3,z4,z138,z5,z6]),(0,[z0,z61,z2,z3,z4,z5,z28])],[(0,[z0,z2,z3,z4,z24,z6,z139]),(0,[z0,z2,z3,z4,z140,z5,z6])],[(1,[z0,z2,z3,z4,z5,z6]),(0,[z141,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z142,z4,z5,z6]),(0,[z0,z143,z2,z3,z4,z5,z6]),(0,[z0,z144,z2,z3,z4,z5,z6])]],
   [[(0,[z84,z0,z2,z145,z4,z5,z6]),(1,[z0,z2,z3,z146,z5,z6]),(0,[z0,z2,z147,z3,z4,z26,z6]),(0,[z0,z148,z2,z3,z4,z5,z6])],[(1,[z2,z3,z4,z26,z24,z6]),(0,[z0,z2,z3,z4,z5,z68,z6]),(0,[z149,z0,z2,z3,z4,z5,z6]),(0,[z37,z0,z2,z3,z4,z150,z6]),(0,[z151,z0,z2,z3,z4,z5,z6]),(0,[z0,z152,z2,z3,z4,z5,z6]),(0,[z0,z2,z153,z3,z4,z5,z6])],[(0,[z84,z0,z2,z3,z4,z5,z6]),(0,[z154,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z155,z4,z5,z6]),(0,[z69,z0,z2,z3,z4,z72,z5]),(0,[z0,z156,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z157]),(1,[z0,z2,z3,z4,z6,z158]),(0,[z0,z2,z3,z4,z5,z159,z6]),(0,[z0,z2,z3,z160,z4,z5,z6])],[(0,[z0,z2,z99,z161,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z162,z6]),(0,[z0,z2,z3,z4,z163,z5,z6]),(0,[z0,z2,z164,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z165,z5,z6]),(0,[z0,z2,z3,z4,z5,z166,z6]),(0,[z0,z2,z54,z3,z4,z5,z6])],[(1,[z0,z2,z3,z4,z167,z6]),(0,[z124,z0,z2,z3,z4,z24,z6]),(0,[z0,z2,z3,z4,z24,z95,z6]),(0,[z0,z2,z3,z4,z72,z24,z6])],[(0,[z168,z0,z2,z105,z4,z5,z6]),(0,[z0,z2,z3,z169,z4,z5,z6]),(0,[z170,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z55,z24,z6]),(0,[z0,z61,z3,z52,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z171])],[(0,[z7,z0,z2,z3,z172,z5,z6]),(0,[z38,z0,z40,z2,z3,z4,z6]),(0,[z0,z2,z3,z173,z4,z5,z127])],[(0,[z0,z2,z105,z3,z4,z24,z6]),(0,[z0,z174,z2,z3,z52,z5,z6]),(0,[z0,z2,z3,z175,z4,z5,z6]),(0,[z0,z176,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z177,z6]),(0,[z0,z2,z3,z173,z4,z8,z6])]],
   [[(0,[z38,z124,z0,z2,z3,z4,z6]),(1,[z0,z2,z3,z4,z178,z6]),(1,[z0,z2,z3,z4,z179,z5]),(0,[z0,z2,z180,z3,z4,z5,z6]),(0,[z181,z0,z2,z3,z4,z5,z6]),(0,[z106,z0,z2,z99,z3,z5,z6]),(1,[z0,z2,z3,z5,z6,z182]),(0,[z0,z2,z3,z4,z183,z8,z6])],[(0,[z0,z0,z2,z3,z4,z5,z6]),(1,[z103,z62,z3,z4,z5,z6]),(0,[z38,z168,z0,z2,z3,z4,z6]),(0,[z39,z0,z2,z3,z184,z5,z6]),(0,[z0,z2,z3,z4,z5,z70,z6])],[(0,[z0,z2,z123,z3,z4,z8,z6]),(0,[z0,z2,z3,z185,z4,z5,z6]),(0,[z0,z62,z3,z4,z5,z6,z28]),(0,[z0,z2,z3,z4,z129,z5,z6]),(0,[z48,z0,z2,z3,z4,z72,z5]),(1,[z0,z174,z3,z52,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z186]),(0,[z187,z0,z2,z3,z4,z5,z6])],[(1,[z0,z2,z188,z4,z5,z6]),(0,[z0,z2,z3,z4,z26,z24,z6]),(0,[z0,z174,z2,z3,z4,z24,z6]),(0,[z0,z2,z3,z4,z26,z53,z6]),(0,[z0,z2,z147,z13,z3,z4,z6]),(0,[z0,z189,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z190]),(0,[z124,z0,z2,z3,z4,z26,z6]),(0,[z38,z0,z2,z3,z4,z150,z6]),(0,[z191,z0,z2,z3,z4,z5,z121])],[(0,[z106,z0,z2,z3,z4,z24,z6]),(0,[z0,z2,z3,z4,z55,z26,z6]),(0,[z0,z2,z3,z4,z192,z5,z6])],[(0,[z84,z0,z2,z188,z4,z5,z6]),(0,[z168,z7,z2,z3,z4,z5,z6]),(0,[z0,z2,z193,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z26,z6,z139]),(1,[z0,z2,z3,z4,z194,z6]),(0,[z0,z2,z3,z4,z5,z195,z6]),(0,[z0,z2,z147,z3,z4,z5,z6]),(0,[z0,z2,z147,z4,z5,z196,z6]),(0,[z0,z2,z3,z4,z5,z6,z197]),(0,[z0,z2,z3,z4,z198,z5,z6]),(0,[z0,z199,z2,z3,z4,z5,z6])],[(0,[z168,z0,z2,z3,z4,z200,z6]),(0,[z0,z2,z3,z161,z4,z8,z6]),(0,[z0,z2,z105,z3,z4,z26,z6]),(0,[z0,z2,z3,z4,z5,z150,z6]),(0,[z0,z201,z2,z3,z4,z5,z6]),(1,[z29,z0,z3,z4,z202,z6]),(0,[z203,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z204,z3,z4,z5,z6]),(0,[z0,z2,z3,z5,z82,z6,z127])]],
   [[(0,[z0,z2,z3,z173,z4,z5,z82])],[(0,[z0,z2,z3,z4,z5,z6,z205]),(0,[z0,z2,z3,z4,z5,z6,z206]),(0,[z0,z2,z3,z4,z207,z8,z6])],[(1,[z84,z123,z3,z4,z5,z6]),(0,[z62,z2,z123,z3,z4,z5,z6]),(0,[z7,z0,z2,z3,z4,z208,z6]),(0,[z94,z0,z2,z3,z4,z8,z6])],[(0,[z209,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z210,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z211,z6]),(0,[z0,z212,z2,z3,z4,z24,z6]),(0,[z0,z2,z3,z4,z26,z26,z6]),(0,[z0,z174,z2,z3,z4,z26,z6]),(1,[z0,z2,z3,z4,z213,z6]),(0,[z0,z2,z99,z147,z4,z5,z6]),(0,[z38,z0,z43,z2,z3,z4,z6])],[(0,[z0,z2,z3,z4,z24,z6,z127]),(0,[z69,z0,z2,z3,z4,z214,z6])],[(1,[z168,z2,z161,z4,z5,z6]),(0,[z106,z0,z2,z3,z4,z26,z6]),(0,[z0,z2,z3,z4,z26,z6,z215]),(0,[z0,z2,z3,z4,z216,z5,z6]),(0,[z0,z217,z2,z3,z4,z5,z6])],[(0,[z218,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z219,z6]),(0,[z38,z0,z2,z3,z15,z4,z6]),(0,[z220,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z221,z6]),(0,[z38,z0,z2,z54,z3,z4,z6]),(0,[z0,z2,z3,z4,z8,z6,z127]),(1,[z0,z222,z3,z4,z5,z6])],[(0,[z168,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z24,z6,z28]),(0,[z0,z2,z3,z4,z24,z57,z6]),(0,[z0,z2,z223,z3,z4,z8,z6])]],
   [[(0,[z0,z2,z99,z3,z15,z5,z6]),(0,[z0,z2,z3,z4,z5,z224,z6]),(1,[z48,z38,z0,z2,z3,z4]),(0,[z0,z2,z3,z4,z5,z225,z6]),(0,[z38,z0,z61,z2,z3,z4,z6]),(0,[z0,z2,z223,z3,z4,z198,z6])],[(0,[z38,z0,z2,z105,z3,z4,z6]),(0,[z0,z2,z226,z3,z4,z24,z6]),(0,[z227,z0,z2,z3,z4,z5,z6]),(0,[z48,z2,z3,z4,z5,z6,z49]),(0,[z69,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z228,z4,z5,z6]),(0,[z38,z0,z2,z27,z3,z4,z6]),(0,[z0,z2,z3,z4,z8,z6,z28]),(0,[z0,z2,z3,z4,z229,z5,z6]),(0,[z230,z0,z2,z3,z4,z5,z6])],[(0,[z124,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z231]),(0,[z0,z2,z3,z4,z72,z5,z6])],[(1,[z0,z2,z3,z4,z232,z6]),(0,[z0,z233,z2,z3,z4,z5,z6]),(0,[z191,z0,z61,z3,z4,z5,z6]),(0,[z0,z2,z234,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z55,z5,z6]),(0,[z0,z2,z3,z4,z6,z158,z127])],[(0,[z0,z2,z235,z3,z4,z5,z6])],[(0,[z84,z0,z2,z3,z4,z5,z236]),(0,[z0,z2,z105,z3,z4,z5,z6]),(0,[z0,z237,z2,z3,z4,z5,z6]),(0,[z0,z2,z13,z3,z4,z24,z6]),(0,[z0,z2,z51,z3,z183,z5,z6]),(0,[z38,z0,z2,z3,z4,z5,z139])],[(0,[z0,z2,z3,z238,z4,z5,z6])],[(0,[z103,z0,z2,z3,z4,z26,z6]),(0,[z38,z103,z0,z2,z3,z4,z6]),(0,[z94,z2,z3,z4,z5,z24,z6]),(0,[z0,z61,z27,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z239,z5,z6]),(0,[z240,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z241,z6])]],
   [[(0,[z242,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z243,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z244])],[(1,[z0,z2,z3,z4,z245,z6]),(0,[z84,z38,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z6,z246]),(0,[z0,z2,z3,z4,z26,z5,z6]),(0,[z0,z2,z3,z4,z247,z26,z6]),(0,[z0,z2,z3,z4,z248,z5,z6]),(0,[z0,z174,z2,z3,z4,z5,z6]),(0,[z0,z63,z61,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z64,z24,z6]),(0,[z0,z40,z2,z249,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z250]),(0,[z38,z0,z2,z3,z4,z6,z21]),(1,[z0,z2,z126,z4,z5,z6])],[(0,[z7,z0,z2,z3,z4,z24,z6]),(0,[z0,z2,z99,z105,z4,z5,z6]),(0,[z0,z2,z3,z75,z4,z5,z6]),(0,[z106,z0,z2,z3,z4,z5,z6])],[(0,[z84,z0,z2,z3,z4,z245,z6]),(0,[z0,z2,z3,z4,z26,z6,z127]),(0,[z106,z0,z2,z3,z173,z5,z6]),(0,[z251,z0,z2,z3,z4,z8,z6]),(0,[z0,z252,z2,z3,z4,z5,z6])],[(0,[z253,z0,z2,z3,z4,z5,z6]),(0,[z0,z40,z254,z3,z4,z5,z6])],[(0,[z0,z2,z3,z255,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z256]),(0,[z0,z2,z257,z3,z4,z5,z6]),(0,[z38,z0,z2,z3,z4,z183,z6]),(0,[z0,z2,z258,z3,z4,z5,z6])],[(0,[z0,z259,z2,z3,z4,z5,z6]),(0,[z0,z260,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z26,z6,z28]),(0,[z0,z2,z3,z261,z4,z26,z6])]],
   [[(0,[z168,z0,z2,z161,z4,z5,z6]),(0,[z0,z2,z223,z161,z4,z5,z6]),(0,[z0,z2,z3,z4,z26,z72,z6]),(0,[z0,z2,z99,z3,z183,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z262])],[(0,[z0,z2,z3,z184,z5,z6,z127]),(0,[z39,z0,z2,z263,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z264]),(0,[z0,z2,z3,z4,z24,z6,z49]),(0,[z0,z212,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z91,z8,z6]),(0,[z0,z265,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z266,z5,z6])],[(0,[z0,z2,z51,z3,z4,z24,z6]),(0,[z0,z2,z3,z4,z64,z26,z6]),(1,[z0,z2,z147,z4,z196,z6]),(1,[z0,z2,z223,z4,z5,z53]),(0,[z267,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z184,z24,z6]),(1,[z0,z2,z268,z4,z5,z6]),(0,[z0,z2,z3,z269,z4,z5,z6]),(0,[z270,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z173,z4,z271,z6])],[(0,[z272,z0,z2,z3,z4,z5,z6]),(0,[z273,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z274,z5,z6])],[(0,[z103,z0,z2,z3,z4,z5,z6]),(0,[z69,z0,z2,z3,z4,z5,z49]),(0,[z275,z0,z2,z3,z4,z5,z6]),(0,[z38,z0,z2,z3,z4,z55,z6]),(1,[z0,z2,z276,z3,z4,z6]),(0,[z277,z0,z2,z3,z4,z5,z6]),(1,[z38,z0,z31,z3,z4,z6]),(0,[z38,z0,z2,z3,z4,z6,z6])],[(0,[z0,z2,z3,z4,z200,z5,z6]),(0,[z0,z278,z2,z3,z4,z5,z6]),(0,[z0,z2,z279,z3,z4,z5,z6]),(0,[z0,z2,z3,z280,z4,z183,z6])],[(0,[z0,z2,z3,z4,z247,z5,z6]),(0,[z0,z2,z226,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z121,z49]),(0,[z281,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z282,z6])]],
   [[(1,[z94,z2,z3,z4,z24,z6]),(0,[z0,z2,z3,z52,z4,z24,z6]),(0,[z0,z2,z3,z4,z5,z6,z6]),(0,[z0,z61,z2,z3,z4,z5,z121]),(0,[z0,z2,z3,z4,z8,z6,z283])],[(0,[z284,z0,z2,z3,z4,z5,z6]),(0,[z124,z0,z2,z3,z4,z219,z6]),(0,[z285,z0,z2,z3,z4,z5,z6]),(0,[z286,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z287,z3,z4,z5,z6]),(0,[z191,z0,z3,z4,z5,z6,z28]),(0,[z38,z0,z2,z3,z4,z288,z6]),(0,[z0,z2,z3,z289,z4,z8,z6])],[(0,[z103,z0,z2,z3,z4,z167,z6]),(0,[z0,z2,z51,z3,z4,z26,z6]),(0,[z290,z0,z2,z3,z4,z5,z6]),(0,[z0,z291,z3,z4,z5,z53,z6]),(0,[z0,z2,z3,z4,z5,z6,z292])],[(0,[z0,z2,z3,z4,z5,z293,z6]),(0,[z294,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z184,z26,z6]),(0,[z38,z0,z2,z3,z4,z196,z6]),(0,[z0,z2,z3,z4,z5,z6,z295])],[(0,[z0,z2,z3,z4,z5,z296,z6]),(0,[z0,z254,z2,z27,z4,z5,z6]),(0,[z297,z0,z2,z3,z4,z8,z6]),(1,[z0,z2,z257,z3,z5,z6]),(0,[z0,z2,z298,z3,z4,z5,z6]),(1,[z0,z2,z4,z5,z112,z6]),(0,[z38,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z5,z6,z299])],[(0,[z0,z2,z3,z4,z26,z213,z6]),(0,[z0,z2,z3,z261,z4,z5,z6]),(0,[z0,z2,z300,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z301])],[(0,[z0,z62,z2,z3,z4,z24,z6]),(0,[z0,z2,z3,z3,z4,z5,z6]),(0,[z39,z0,z2,z3,z4,z8,z6]),(0,[z38,z0,z2,z3,z4,z5,z28]),(0,[z0,z2,z3,z4,z5,z196,z6])],[(0,[z0,z2,z3,z4,z302,z5,z6]),(0,[z0,z63,z3,z4,z5,z6,z28]),(0,[z303,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z304,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z305]),(0,[z38,z0,z2,z223,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z8,z6])]],
   [[(0,[z0,z2,z306,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z24,z121,z6]),(0,[z307,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z52,z4,z26,z6]),(0,[z0,z2,z3,z4,z64,z5,z6]),(0,[z308,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z309,z5,z6]),(0,[z0,z2,z3,z4,z26,z6,z49]),(0,[z0,z2,z3,z4,z5,z310,z6]),(0,[z0,z2,z3,z4,z5,z6,z311])],[(0,[z0,z2,z3,z312,z4,z5,z6]),(0,[z0,z2,z3,z4,z313,z5,z6]),(0,[z0,z2,z314,z3,z4,z26,z6]),(0,[z0,z2,z3,z4,z315,z5,z6]),(0,[z0,z2,z3,z4,z316,z5,z6]),(0,[z0,z2,z317,z3,z4,z5,z6]),(0,[z0,z2,z276,z3,z4,z5,z6]),(0,[z38,z0,z2,z3,z4,z14,z6]),(0,[z38,z0,z2,z3,z4,z82,z6])],[(0,[z318,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z202,z24,z6]),(0,[z0,z2,z3,z4,z319,z5,z6]),(0,[z0,z320,z2,z3,z4,z8,z6])],[(0,[z321,z0,z2,z3,z4,z24,z6]),(0,[z0,z2,z3,z4,z23,z5,z6]),(0,[z0,z2,z322,z3,z4,z5,z6]),(0,[z0,z2,z3,z280,z4,z8,z6]),(0,[z0,z323,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z324]),(0,[z38,z0,z2,z31,z3,z4,z6])],[(0,[z0,z2,z3,z4,z5,z82,z6])],[(0,[z0,z62,z2,z3,z4,z26,z6]),(0,[z0,z2,z325,z3,z4,z5,z6]),(0,[z326,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z51,z25,z4,z5,z6]),(0,[z327,z0,z2,z3,z4,z8,z6])],[(0,[z328,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z329,z6]),(0,[z0,z2,z3,z4,z5,z6,z330])]],
   [[(1,[z0,z2,z145,z4,z5,z6]),(0,[z0,z2,z3,z4,z331,z5,z6]),(0,[z0,z2,z332,z3,z4,z5,z6]),(1,[z227,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z57,z8,z6]),(0,[z0,z2,z3,z4,z5,z333,z6]),(1,[z0,z61,z3,z4,z5,z121]),(0,[z0,z2,z51,z3,z4,z5,z6])],[(0,[z0,z2,z334,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z184,z5,z6]),(0,[z0,z2,z257,z3,z5,z6,z21]),(0,[z0,z2,z3,z4,z5,z6,z335])],[(0,[z0,z2,z3,z188,z4,z5,z6]),(0,[z38,z0,z2,z123,z3,z4,z6]),(1,[z0,z2,z135,z4,z5,z6]),(0,[z0,z2,z3,z336,z4,z5,z6]),(0,[z337,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z280,z4,z14,z6])],[(0,[z0,z2,z3,z4,z73,z5,z6]),(0,[z0,z338,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z339,z26,z6]),(0,[z0,z2,z3,z4,z202,z26,z6]),(1,[z0,z2,z317,z3,z5,z6])],[(0,[z0,z2,z161,z4,z5,z6,z21]),(0,[z0,z2,z105,z249,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z340]),(0,[z0,z2,z3,z4,z341,z5,z6])],[(0,[z0,z2,z263,z3,z4,z5,z6]),(0,[z48,z0,z342,z3,z4,z5,z6]),(0,[z0,z2,z343,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z344,z5,z6]),(0,[z29,z38,z0,z2,z3,z4,z6]),(0,[z106,z0,z2,z51,z3,z5,z6]),(0,[z0,z2,z3,z4,z196,z8,z6]),(0,[z0,z2,z3,z4,z5,z345,z6]),(0,[z22,z38,z0,z2,z3,z4,z6])],[(0,[z0,z346,z2,z3,z4,z5,z6]),(0,[z0,z347,z3,z161,z4,z5,z6]),(0,[z39,z2,z3,z15,z4,z5,z6]),(0,[z0,z50,z2,z3,z4,z5,z6]),(0,[z0,z254,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z52,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z110,z6]),(0,[z0,z2,z3,z4,z5,z207,z6]),(0,[z0,z2,z3,z4,z5,z348,z6]),(0,[z0,z222,z2,z3,z4,z5,z6])],[(0,[z349,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z249,z4,z24,z6]),(0,[z29,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z350,z4,z5,z6]),(0,[z0,z2,z351,z3,z4,z5,z6]),(0,[z0,z2,z352,z3,z4,z5,z6]),(0,[z0,z2,z13,z3,z280,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z26,z121,z6]),(0,[z0,z2,z314,z3,z4,z5,z6]),(0,[z48,z0,z2,z3,z4,z5,z150]),(0,[z0,z2,z3,z4,z288,z5,z6]),(0,[z0,z353,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z354]),(0,[z0,z2,z3,z15,z5,z6,z127]),(0,[z0,z2,z3,z4,z5,z6,z355]),(0,[z0,z2,z99,z3,z91,z5,z6])],[(0,[z0,z2,z27,z3,z4,z24,z6]),(0,[z0,z2,z3,z173,z4,z24,z6]),(0,[z227,z0,z2,z3,z4,z5,z24]),(0,[z0,z2,z3,z4,z5,z6,z356]),(0,[z0,z2,z3,z4,z357,z5,z6]),(0,[z38,z0,z2,z3,z56,z4,z6])],[(0,[z0,z2,z3,z358,z4,z5,z6]),(0,[z0,z2,z3,z4,z359,z5,z6]),(0,[z0,z2,z3,z4,z360,z5,z6]),(0,[z0,z43,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z333,z8,z6])],[(0,[z0,z62,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z361,z6]),(2,[z227,z0,z2,z3,z4]),(0,[z0,z2,z3,z362,z4,z5,z6]),(0,[z38,z0,z2,z147,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z363,z6])],[(0,[z364,z0,z2,z3,z4,z5,z6]),(0,[z7,z2,z105,z3,z4,z5,z6]),(0,[z0,z2,z102,z3,z4,z5,z6]),(0,[z0,z40,z2,z27,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z365,z6]),(0,[z0,z2,z3,z4,z5,z366,z6]),(0,[z0,z2,z3,z173,z4,z78,z6]),(0,[z0,z2,z3,z4,z367,z5,z6])],[(0,[z0,z3,z4,z5,z57,z6,z28]),(0,[z0,z2,z3,z4,z5,z368,z6])],[(0,[z0,z2,z369,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z370,z5,z6]),(0,[z2,z3,z4,z26,z5,z24,z6]),(0,[z0,z2,z3,z249,z4,z26,z6]),(0,[z0,z2,z3,z4,z371,z26,z6]),(1,[z0,z2,z3,z4,z248,z6]),(0,[z0,z2,z3,z4,z8,z150,z6]),(0,[z0,z2,z372,z3,z4,z5,z6])]],
   [[],[(0,[z0,z123,z3,z4,z5,z6,z28]),(0,[z0,z2,z3,z373,z4,z5,z6]),(0,[z0,z2,z3,z4,z339,z5,z6]),(0,[z0,z2,z3,z4,z5,z374,z6]),(0,[z0,z2,z3,z375,z4,z5,z6]),(0,[z0,z2,z376,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z202,z5,z6])],[(0,[z321,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z377,z6]),(0,[z124,z2,z3,z4,z184,z5,z6]),(0,[z0,z2,z27,z3,z4,z26,z6]),(0,[z0,z2,z3,z173,z4,z26,z6]),(0,[z378,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z379]),(0,[z0,z2,z3,z4,z380,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z381])],[(0,[z0,z2,z161,z25,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z382]),(0,[z0,z383,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z384]),(0,[z38,z0,z2,z3,z385,z4,z6])],[(0,[z84,z0,z62,z3,z4,z5,z6]),(0,[z386,z0,z2,z3,z4,z5,z6]),(0,[z168,z2,z3,z161,z4,z5,z6]),(0,[z7,z0,z2,z3,z4,z232,z6]),(0,[z94,z0,z2,z3,z4,z24,z6]),(0,[z0,z2,z387,z3,z4,z5,z6]),(1,[z0,z2,z4,z5,z6,z388]),(0,[z0,z2,z3,z4,z5,z389,z6])],[(1,[z0,z2,z263,z4,z5,z6]),(0,[z390,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z391,z4,z5,z6]),(0,[z0,z2,z392,z3,z4,z5,z6])],[(0,[z38,z0,z254,z2,z3,z4,z6]),(0,[z393,z0,z2,z3,z4,z5,z6]),(0,[z0,z394,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z104,z6]),(0,[z0,z2,z3,z4,z395,z5,z6])],[(1,[z69,z2,z3,z4,z5,z150]),(0,[z0,z2,z3,z4,z5,z6,z396]),(0,[z0,z2,z3,z4,z397,z5,z6])],[(0,[z84,z0,z63,z3,z4,z5,z6]),(0,[z398,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z399,z6])],[(1,[z0,z2,z3,z4,z200,z6]),(0,[z0,z2,z400,z3,z4,z5,z6]),(0,[z0,z401,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z271,z6])],[(0,[z39,z0,z2,z3,z15,z5,z6]),(0,[z0,z2,z3,z4,z5,z402,z6]),(0,[z69,z0,z2,z3,z4,z24,z6]),(0,[z29,z0,z3,z4,z202,z5,z6]),(0,[z0,z2,z3,z403,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z404])],[(1,[z0,z2,z3,z4,z5,z236]),(0,[z191,z0,z2,z3,z4,z24,z6]),(0,[z0,z2,z3,z4,z26,z405,z6]),(0,[z0,z2,z3,z4,z371,z5,z6]),(0,[z0,z2,z3,z249,z4,z5,z6]),(0,[z406,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z147,z54,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z407])],[(0,[z0,z2,z3,z4,z5,z408,z6]),(0,[z0,z2,z3,z4,z5,z409,z6]),(0,[z0,z50,z2,z3,z4,z6,z49]),(0,[z410,z0,z2,z3,z4,z5,z6]),(0,[z411,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z121,z8,z6]),(0,[z38,z0,z2,z3,z4,z5,z8])],[(1,[z0,z383,z3,z4,z5,z6]),(0,[z0,z40,z2,z3,z4,z8,z6]),(0,[z412,z0,z2,z3,z4,z5,z6]),(0,[z0,z63,z2,z3,z52,z5,z6]),(0,[z0,z2,z413,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z388,z127])]],
   [[(0,[z414,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z27,z3,z4,z5,z6]),(0,[z0,z2,z54,z3,z4,z55,z6]),(0,[z0,z2,z3,z173,z4,z5,z6])],[(0,[z0,z2,z3,z4,z415,z5,z6]),(1,[z0,z2,z51,z25,z5,z6]),(1,[z38,z0,z2,z3,z4,z6])],[(0,[z0,z2,z416,z3,z4,z5,z6]),(0,[z0,z2,z3,z268,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z417,z6])],[(0,[z0,z63,z2,z3,z4,z24,z6]),(0,[z0,z2,z3,z4,z24,z6,z21]),(1,[z41,z2,z3,z4,z26,z6]),(0,[z418,z0,z2,z3,z4,z26,z6]),(1,[z0,z2,z3,z419,z5,z6]),(0,[z0,z2,z3,z4,z5,z420,z6]),(0,[z0,z2,z3,z421,z4,z5,z6]),(1,[z0,z3,z4,z5,z6,z324]),(1,[z0,z2,z3,z4,z8,z6])],[(0,[z48,z0,z2,z3,z4,z24,z6]),(1,[z0,z2,z99,z91,z5,z6]),(1,[z0,z2,z3,z4,z198,z6]),(0,[z0,z2,z422,z3,z4,z5,z6])],[(0,[z0,z61,z123,z3,z4,z5,z6]),(0,[z191,z0,z2,z3,z4,z26,z6]),(0,[z48,z38,z0,z2,z3,z4,z5]),(0,[z423,z0,z2,z3,z4,z5,z6]),(0,[z38,z0,z2,z3,z249,z4,z6]),(0,[z38,z0,z2,z3,z4,z202,z6]),(0,[z0,z2,z3,z4,z8,z6,z21])],[(0,[z84,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z424,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z425,z6]),(0,[z0,z2,z426,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z427,z5,z6]),(0,[z0,z2,z317,z3,z5,z196,z6]),(0,[z0,z2,z13,z3,z5,z14,z6]),(0,[z0,z2,z3,z4,z428,z5,z6])],[(0,[z0,z2,z3,z15,z4,z24,z6]),(0,[z0,z2,z3,z4,z5,z6,z429]),(0,[z0,z2,z430,z3,z4,z5,z6]),(0,[z0,z2,z54,z3,z4,z8,z6]),(1,[z0,z2,z13,z3,z14,z6]),(0,[z0,z2,z3,z4,z72,z5,z139])]],
   [[(0,[z0,z2,z3,z4,z5,z431,z6]),(0,[z0,z2,z432,z3,z4,z5,z6]),(0,[z0,z2,z13,z3,z4,z26,z6]),(0,[z433,z0,z2,z3,z4,z5,z6]),(0,[z434,z0,z2,z3,z4,z5,z6]),(0,[z29,z0,z2,z3,z4,z5,z435]),(0,[z0,z2,z4,z5,z53,z6,z21]),(0,[z0,z2,z223,z3,z4,z345,z6])],[(0,[z0,z2,z3,z436,z4,z5,z6]),(0,[z48,z0,z81,z3,z4,z5,z6]),(0,[z437,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z438,z4,z5,z6]),(0,[z38,z0,z2,z3,z4,z5,z121]),(0,[z0,z2,z3,z4,z5,z6,z439]),(1,[z0,z2,z3,z280,z183,z6])],[(0,[z0,z2,z3,z440,z4,z5,z6]),(0,[z0,z2,z3,z4,z26,z57,z6]),(0,[z0,z254,z27,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z441,z6]),(0,[z442,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z443,z3,z4,z5,z6]),(0,[z41,z0,z2,z3,z4,z24,z6]),(0,[z0,z63,z2,z3,z4,z26,z6]),(0,[z0,z2,z3,z4,z444,z6,z49]),(0,[z0,z2,z3,z4,z445,z5,z6]),(0,[z0,z2,z147,z3,z4,z55,z6]),(0,[z0,z2,z3,z4,z5,z446,z6]),(0,[z0,z2,z3,z4,z5,z112,z6]),(1,[z0,z2,z3,z4,z6,z330])],[(0,[z0,z2,z3,z4,z91,z24,z6]),(0,[z48,z0,z2,z3,z4,z26,z6]),(0,[z0,z320,z2,z3,z4,z202,z6]),(0,[z0,z3,z4,z5,z121,z6,z28]),(0,[z447,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z448,z6]),(0,[z0,z2,z3,z4,z5,z49,z28]),(0,[z0,z2,z3,z4,z5,z444,z6])],[(0,[z7,z0,z2,z3,z4,z26,z6]),(0,[z0,z2,z3,z4,z449,z24,z6]),(0,[z0,z2,z3,z4,z419,z5,z6]),(0,[z0,z450,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z451,z5,z6]),(0,[z0,z2,z223,z3,z4,z5,z53])],[(0,[z0,z2,z3,z15,z4,z26,z6]),(0,[z0,z2,z3,z4,z26,z452,z6]),(0,[z453,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z84,z0,z3,z52,z4,z5,z6]),(0,[z103,z62,z2,z3,z4,z5,z6]),(0,[z0,z454,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z68,z6]),(0,[z0,z2,z3,z4,z455,z5,z6]),(0,[z0,z2,z3,z4,z8,z6,z6])],[(0,[z456,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z9,z6]),(0,[z418,z0,z2,z3,z4,z5,z6]),(0,[z48,z0,z2,z3,z108,z5,z6]),(0,[z0,z2,z3,z4,z221,z5,z6]),(0,[z38,z0,z2,z99,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z457,z6]),(0,[z38,z0,z31,z3,z4,z5,z6])],[(0,[z39,z124,z2,z3,z4,z5,z6]),(0,[z69,z0,z2,z3,z4,z5,z6]),(0,[z38,z0,z2,z3,z52,z4,z6]),(1,[z0,z2,z3,z4,z110,z6]),(0,[z0,z2,z147,z3,z4,z8,z6]),(0,[z0,z2,z458,z3,z4,z5,z6]),(0,[z0,z2,z3,z280,z183,z5,z6])],[(0,[z0,z347,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z459,z6]),(0,[z41,z0,z2,z3,z4,z26,z6]),(0,[z0,z81,z2,z3,z4,z5,z6]),(0,[z0,z2,z460,z3,z4,z5,z6]),(0,[z191,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z99,z4,z55,z5,z6]),(0,[z0,z2,z461,z3,z4,z5,z6]),(0,[z38,z0,z43,z3,z4,z5,z6])],[(0,[z462,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z91,z26,z6]),(0,[z37,z0,z2,z3,z4,z26,z6]),(0,[z0,z2,z463,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z24,z8,z6]),(0,[z0,z2,z3,z4,z5,z150,z28]),(0,[z0,z2,z464,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z465,z6]),(0,[z0,z2,z3,z4,z5,z6,z466]),(0,[z0,z467,z2,z3,z4,z5,z6]),(1,[z38,z0,z43,z3,z4,z6])],[(0,[z84,z103,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z468,z6]),(0,[z0,z61,z3,z4,z5,z121,z6]),(0,[z0,z2,z13,z3,z4,z5,z6])],[(0,[z38,z0,z2,z3,z4,z24,z6]),(0,[z0,z2,z469,z3,z4,z5,z6]),(0,[z38,z0,z2,z3,z4,z53,z6]),(0,[z0,z2,z3,z4,z8,z8,z6])]],
   [[(0,[z0,z2,z99,z3,z4,z24,z6]),(0,[z0,z2,z470,z3,z4,z26,z6]),(1,[z0,z2,z3,z4,z70,z6]),(0,[z69,z2,z3,z4,z5,z150,z6]),(0,[z471,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z51,z3,z25,z5,z6])],[(0,[z472,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z473,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z474,z5,z6]),(0,[z0,z63,z2,z3,z4,z5,z6]),(0,[z0,z2,z31,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z95,z8,z6])],[(0,[z0,z2,z3,z4,z5,z236,z6]),(0,[z0,z2,z3,z4,z5,z24,z6]),(0,[z48,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z53,z6]),(0,[z38,z0,z2,z3,z4,z6,z139])],[(0,[z0,z2,z3,z4,z24,z82,z6]),(0,[z0,z2,z3,z4,z24,z14,z6]),(1,[z0,z254,z27,z4,z5,z6]),(0,[z475,z0,z2,z3,z4,z5,z6]),(0,[z476,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z477,z6])],[(0,[z7,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z161,z249,z4,z5,z6]),(0,[z478,z0,z2,z3,z4,z5,z6]),(0,[z297,z0,z2,z4,z5,z6,z21]),(0,[z479,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z15,z4,z5,z6]),(0,[z0,z2,z3,z52,z184,z5,z6]),(0,[z0,z2,z3,z4,z24,z6,z128]),(0,[z38,z69,z0,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z6,z480]),(0,[z0,z2,z3,z4,z5,z6,z139])],[(0,[z0,z2,z3,z15,z173,z5,z6]),(0,[z0,z320,z2,z3,z4,z24,z6]),(0,[z481,z0,z2,z3,z4,z5,z6]),(0,[z482,z0,z2,z3,z4,z5,z6]),(0,[z38,z0,z2,z422,z3,z4,z6])],[(0,[z0,z2,z3,z4,z92,z5,z6]),(0,[z0,z2,z483,z3,z4,z5,z6]),(0,[z0,z2,z3,z484,z4,z5,z6]),(0,[z0,z485,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z5,z6,z182,z21]),(0,[z0,z2,z3,z4,z8,z6,z330])]],
   [[(0,[z103,z0,z62,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z486,z6]),(0,[z0,z2,z3,z4,z5,z487,z6]),(0,[z0,z2,z99,z3,z4,z26,z6]),(0,[z0,z40,z3,z249,z4,z5,z6])],[(0,[z168,z0,z2,z3,z4,z409,z6]),(0,[z0,z2,z105,z3,z4,z8,z6]),(0,[z41,z0,z2,z3,z4,z5,z6]),(0,[z0,z61,z2,z3,z4,z24,z6]),(0,[z0,z2,z3,z4,z5,z488,z6]),(0,[z0,z2,z489,z3,z4,z5,z6]),(0,[z44,z0,z2,z3,z4,z5,z6]),(0,[z490,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z491,z6]),(0,[z0,z2,z3,z4,z5,z6,z492]),(0,[z0,z2,z493,z3,z4,z5,z6]),(0,[z38,z0,z144,z2,z3,z4,z6]),(0,[z494,z0,z2,z3,z4,z8,z6])],[(0,[z0,z2,z495,z3,z4,z5,z6]),(0,[z0,z2,z3,z172,z4,z5,z6]),(0,[z496,z0,z2,z3,z4,z5,z6]),(0,[z37,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z91,z5,z6])],[(0,[z0,z2,z145,z3,z4,z5,z6]),(0,[z0,z2,z497,z3,z4,z5,z6]),(0,[z498,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z95,z6]),(0,[z69,z0,z2,z3,z4,z5,z150]),(0,[z499,z0,z2,z3,z4,z5,z6]),(0,[z297,z0,z2,z223,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z500]),(0,[z0,z2,z3,z4,z24,z162,z6]),(0,[z0,z2,z3,z4,z449,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z215]),(0,[z0,z2,z501,z3,z4,z5,z6]),(0,[z502,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z435]),(0,[z503,z0,z2,z3,z4,z5,z6]),(0,[z504,z0,z2,z3,z4,z5,z6])],[(0,[z103,z0,z63,z3,z4,z5,z6]),(0,[z0,z2,z59,z3,z4,z5,z6])],[(0,[z0,z505,z2,z3,z4,z5,z6]),(0,[z0,z2,z470,z3,z4,z5,z6]),(0,[z0,z320,z2,z3,z4,z26,z6]),(0,[z0,z2,z3,z506,z4,z5,z6]),(0,[z106,z0,z2,z3,z4,z5,z127])],[(0,[z507,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z179,z24,z6]),(0,[z0,z2,z3,z4,z5,z508,z6]),(1,[z0,z2,z509,z4,z5,z6]),(0,[z510,z0,z2,z3,z4,z5,z6]),(0,[z106,z0,z2,z3,z4,z8,z6])]],
   [[(0,[z0,z252,z2,z3,z4,z8,z6])],[(0,[z0,z2,z3,z511,z4,z5,z6]),(0,[z0,z2,z3,z4,z512,z5,z6]),(0,[z0,z2,z3,z4,z5,z513,z6]),(0,[z0,z254,z2,z3,z4,z24,z6]),(0,[z0,z2,z18,z3,z4,z24,z6]),(0,[z0,z61,z2,z3,z4,z26,z6]),(0,[z0,z2,z25,z4,z55,z5,z6])],[(0,[z84,z0,z27,z3,z4,z5,z6]),(0,[z0,z3,z52,z4,z64,z5,z6]),(1,[z0,z2,z514,z3,z4,z6]),(0,[z22,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z289,z4,z5,z6])],[(0,[z0,z2,z3,z4,z26,z14,z6]),(0,[z29,z0,z61,z3,z4,z5,z6]),(0,[z297,z0,z2,z25,z4,z5,z6]),(0,[z297,z0,z2,z3,z4,z5,z53]),(0,[z0,z2,z3,z515,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z516,z6])],[(0,[z517,z0,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z202,z5,z57,z6]),(0,[z29,z0,z2,z3,z4,z5,z310]),(0,[z0,z2,z99,z13,z3,z5,z6]),(0,[z0,z2,z3,z518,z4,z5,z6]),(0,[z0,z2,z276,z3,z4,z6,z21]),(0,[z0,z2,z3,z4,z5,z6,z388]),(0,[z519,z0,z2,z3,z4,z5,z6])],[(0,[z520,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z105,z223,z4,z5,z6]),(1,[z38,z69,z0,z2,z3,z4]),(0,[z0,z521,z2,z3,z4,z5,z6]),(0,[z0,z2,z522,z3,z4,z5,z6]),(0,[z523,z0,z2,z3,z4,z5,z6]),(0,[z38,z0,z2,z3,z173,z4,z6])],[(0,[z0,z2,z3,z4,z183,z24,z6]),(0,[z0,z2,z3,z4,z524,z5,z6]),(0,[z0,z2,z3,z4,z5,z525,z6]),(0,[z0,z2,z99,z3,z4,z5,z6]),(1,[z0,z291,z3,z4,z5,z6]),(0,[z453,z38,z0,z2,z3,z4,z6])],[(1,[z0,z347,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z526]),(0,[z0,z2,z3,z527,z4,z5,z6]),(0,[z0,z528,z2,z3,z4,z5,z6]),(0,[z0,z174,z3,z52,z4,z5,z6]),(0,[z0,z2,z99,z4,z5,z53,z6])]],
   [[(0,[z0,z2,z123,z3,z4,z24,z6]),(0,[z0,z2,z3,z4,z5,z5,z6]),(0,[z0,z2,z3,z4,z24,z150,z6]),(0,[z0,z2,z529,z3,z4,z5,z6]),(0,[z29,z0,z320,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z530,z6]),(0,[z38,z297,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z531,z5,z6]),(0,[z0,z291,z2,z3,z4,z5,z6])],[(0,[z103,z0,z2,z3,z4,z8,z6]),(0,[z2,z105,z3,z161,z4,z5,z6]),(0,[z0,z2,z3,z4,z532,z5,z6]),(0,[z0,z2,z3,z4,z5,z533,z6]),(0,[z534,z0,z2,z3,z4,z5,z6])],[(0,[z535,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z67,z4,z24,z6]),(0,[z0,z174,z2,z3,z64,z5,z6]),(0,[z0,z2,z3,z536,z4,z5,z6]),(0,[z0,z2,z537,z3,z4,z5,z6])],[(0,[z38,z0,z2,z3,z4,z6,z28]),(0,[z0,z2,z3,z4,z14,z8,z6]),(0,[z0,z2,z3,z4,z5,z6,z538]),(0,[z0,z2,z3,z4,z5,z6,z127]),(0,[z0,z2,z3,z4,z5,z6,z158]),(0,[z0,z2,z3,z173,z5,z82,z6]),(0,[z285,z38,z0,z2,z3,z4,z6])],[(0,[z124,z0,z2,z3,z184,z5,z6]),(0,[z0,z2,z3,z4,z95,z150,z6]),(0,[z0,z320,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z53,z8,z6]),(0,[z290,z38,z0,z2,z3,z4,z6]),(0,[z38,z0,z2,z3,z4,z72,z6]),(1,[z0,z2,z3,z4,z72,z8])],[(0,[z0,z2,z3,z161,z4,z24,z6]),(1,[z0,z2,z3,z4,z208,z6]),(0,[z38,z0,z174,z2,z3,z4,z6]),(0,[z0,z320,z3,z4,z5,z57,z6]),(1,[z0,z2,z3,z5,z539,z6]),(0,[z0,z2,z3,z540,z4,z5,z6])],[(0,[z0,z2,z3,z4,z183,z26,z6]),(0,[z0,z2,z3,z4,z5,z57,z6]),(0,[z0,z2,z3,z4,z5,z6,z28]),(0,[z0,z2,z509,z4,z5,z14,z6])],[(0,[z541,z0,z2,z3,z4,z5,z6]),(0,[z542,z0,z2,z3,z4,z5,z6]),(0,[z0,z61,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z6,z439,z21])]],
   [[(0,[z84,z0,z40,z3,z4,z5,z6]),(0,[z0,z2,z123,z3,z4,z26,z6]),(0,[z0,z61,z3,z4,z5,z57,z6]),(0,[z0,z2,z13,z51,z3,z5,z6]),(0,[z0,z2,z3,z25,z4,z8,z6]),(0,[z543,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z544,z5,z6]),(0,[z0,z2,z3,z4,z5,z545,z6])],[(0,[z0,z2,z3,z4,z5,z6,z546]),(0,[z0,z2,z3,z4,z5,z178,z6]),(0,[z41,z2,z3,z4,z26,z5,z6]),(0,[z0,z547,z2,z3,z4,z5,z6]),(0,[z303,z38,z0,z2,z3,z4,z6])],[(0,[z0,z548,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z549,z4,z5,z6]),(0,[z0,z2,z550,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z551,z6])],[(0,[z103,z0,z3,z52,z4,z5,z6]),(0,[z552,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z553,z5,z6]),(0,[z0,z2,z554,z3,z4,z5,z6]),(0,[z0,z2,z3,z555,z4,z5,z6])],[(0,[z0,z2,z3,z4,z64,z8,z6]),(0,[z0,z556,z2,z3,z4,z5,z6])],[(0,[z168,z0,z2,z3,z4,z24,z6]),(0,[z0,z2,z3,z161,z4,z26,z6]),(0,[z0,z2,z223,z3,z4,z24,z6]),(0,[z0,z2,z3,z4,z179,z5,z6]),(0,[z0,z2,z557,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z558,z5,z6]),(0,[z559,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z560]),(0,[z0,z2,z3,z385,z4,z5,z6])],[(0,[z0,z2,z3,z4,z561,z5,z6]),(0,[z0,z2,z3,z562,z4,z5,z6]),(0,[z563,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z564,z5,z6]),(0,[z0,z2,z126,z3,z4,z5,z6])],[(0,[z84,z2,z123,z3,z4,z5,z6]),(0,[z0,z2,z3,z565,z4,z5,z6]),(0,[z0,z254,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z194,z6])]],
   [[(0,[z94,z0,z2,z3,z4,z26,z6]),(0,[z41,z38,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z26,z150,z6]),(0,[z0,z2,z566,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z539,z6]),(0,[z38,z0,z2,z3,z280,z4,z6]),(0,[z490,z38,z0,z2,z3,z4,z6])],[(1,[z0,z2,z3,z312,z5,z6]),(0,[z0,z2,z3,z4,z5,z567,z6]),(1,[z0,z2,z3,z4,z214,z6]),(0,[z0,z568,z2,z3,z4,z5,z6]),(0,[z29,z0,z3,z4,z5,z6,z28]),(0,[z0,z2,z3,z4,z5,z6,z569]),(0,[z0,z2,z469,z3,z4,z91,z6])],[(0,[z570,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z571]),(0,[z0,z572,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z82,z6,z324])],[(0,[z0,z2,z342,z3,z4,z5,z6]),(0,[z0,z40,z61,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z573]),(0,[z574,z0,z2,z3,z4,z5,z6])],[(0,[z84,z0,z2,z3,z312,z5,z6]),(0,[z124,z0,z2,z3,z15,z5,z6]),(0,[z0,z2,z3,z4,z5,z213,z6]),(0,[z0,z2,z3,z4,z183,z5,z6])],[(0,[z168,z0,z2,z3,z4,z26,z6]),(0,[z0,z2,z3,z4,z184,z8,z6]),(0,[z0,z2,z223,z3,z4,z26,z6]),(0,[z2,z3,z4,z5,z150,z6,z49]),(0,[z38,z0,z2,z3,z4,z6,z49]),(0,[z38,z191,z0,z2,z3,z4,z6])],[(0,[z0,z2,z123,z3,z4,z5,z6]),(0,[z0,z575,z2,z3,z4,z5,z6]),(0,[z48,z0,z2,z268,z4,z5,z6]),(0,[z0,z61,z2,z3,z4,z194,z6]),(0,[z0,z2,z3,z4,z5,z576,z6]),(0,[z510,z38,z0,z2,z3,z4,z6])],[(0,[z0,z2,z3,z4,z577,z5,z6]),(0,[z69,z0,z2,z3,z4,z26,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z6,z49]),(1,[z0,z2,z3,z4,z5,z310]),(0,[z0,z2,z3,z4,z5,z578,z6]),(0,[z0,z2,z579,z3,z4,z5,z6]),(0,[z0,z2,z223,z3,z4,z5,z21])],[(0,[z84,z0,z2,z3,z4,z24,z6]),(0,[z0,z2,z580,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z26,z224,z6]),(0,[z0,z2,z3,z4,z5,z6,z581]),(0,[z582,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z54,z3,z4,z196,z6]),(0,[z0,z3,z4,z5,z53,z6,z560])],[(0,[z0,z2,z3,z4,z163,z24,z6]),(0,[z0,z2,z54,z3,z4,z24,z6]),(0,[z0,z27,z3,z249,z4,z5,z6]),(0,[z0,z2,z3,z52,z4,z8,z6]),(0,[z0,z2,z3,z4,z5,z6,z583])],[(0,[z0,z2,z3,z4,z5,z6,z584]),(0,[z0,z2,z3,z161,z4,z5,z6]),(0,[z585,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z586,z3,z4,z26,z6]),(0,[z0,z2,z587,z3,z4,z5,z6]),(0,[z0,z2,z3,z588,z4,z5,z6]),(0,[z0,z2,z3,z589,z4,z5,z6]),(0,[z0,z222,z3,z4,z5,z82,z6])],[(0,[z0,z2,z3,z4,z5,z232,z6]),(1,[z7,z2,z105,z4,z5,z6]),(0,[z0,z2,z3,z590,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z591]),(0,[z106,z0,z2,z3,z5,z6,z127])],[(0,[z39,z0,z2,z3,z4,z309,z6]),(0,[z0,z2,z3,z4,z5,z6,z592]),(0,[z0,z2,z3,z4,z5,z6,z283])],[(0,[z7,z0,z2,z161,z4,z5,z6]),(0,[z94,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z593,z6]),(0,[z0,z61,z2,z3,z4,z221,z6]),(0,[z38,z0,z2,z51,z3,z4,z6]),(0,[z0,z2,z4,z55,z5,z196,z6]),(0,[z594,z0,z2,z3,z4,z5,z6]),(1,[z38,z0,z2,z3,z4,z139])],[(0,[z0,z595,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z596])]],
   [[(0,[z0,z62,z2,z3,z4,z8,z6]),(1,[z0,z2,z3,z4,z179,z24]),(0,[z0,z2,z3,z597,z4,z5,z6]),(0,[z0,z2,z3,z598,z4,z5,z6]),(1,[z0,z2,z3,z173,z5,z82]),(1,[z0,z144,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z545,z8,z6])],[(0,[z0,z2,z3,z4,z599,z5,z6]),(0,[z0,z2,z3,z4,z167,z5,z6]),(0,[z0,z2,z3,z600,z4,z5,z6]),(0,[z0,z601,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z602,z4,z5,z6]),(0,[z603,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z245,z6]),(0,[z38,z0,z2,z3,z161,z4,z6]),(1,[z0,z320,z3,z4,z57,z6])],[(0,[z168,z0,z2,z3,z4,z5,z6]),(0,[z0,z604,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z72,z5,z121]),(0,[z0,z2,z223,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z605])],[(0,[z606,z0,z2,z3,z4,z5,z6]),(0,[z607,z0,z2,z3,z4,z5,z6]),(1,[z227,z0,z2,z3,z4,z24]),(0,[z38,z0,z2,z3,z4,z121,z6]),(0,[z0,z2,z147,z3,z4,z196,z6]),(1,[z0,z2,z3,z4,z345,z6]),(0,[z0,z2,z223,z4,z5,z53,z6]),(0,[z608,z0,z2,z3,z4,z5,z6])],[(0,[z103,z0,z27,z3,z4,z5,z6]),(0,[z0,z2,z609,z3,z4,z5,z6]),(0,[z0,z3,z562,z4,z184,z5,z6]),(0,[z0,z2,z147,z3,z4,z24,z6]),(0,[z0,z2,z3,z4,z5,z6,z435]),(0,[z0,z2,z3,z4,z202,z8,z6])],[(0,[z0,z2,z3,z4,z26,z6,z21]),(0,[z0,z2,z51,z3,z5,z82,z6])],[(0,[z0,z2,z3,z4,z5,z610,z6]),(0,[z0,z2,z611,z3,z4,z5,z6]),(1,[z0,z2,z3,z92,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z612]),(0,[z0,z2,z3,z4,z24,z196,z6]),(0,[z0,z2,z3,z4,z5,z121,z6]),(0,[z38,z0,z2,z3,z4,z91,z6]),(0,[z0,z2,z613,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z8,z6,z299])]],
   [[(0,[z0,z2,z3,z4,z24,z53,z6]),(0,[z0,z2,z99,z51,z4,z5,z6]),(0,[z0,z2,z3,z4,z8,z6,z301])],[(0,[z0,z2,z586,z3,z4,z5,z6]),(0,[z0,z614,z2,z3,z4,z5,z6]),(0,[z0,z40,z3,z4,z5,z6,z28]),(0,[z0,z2,z3,z4,z615,z5,z6])],[(0,[z0,z2,z51,z3,z184,z5,z6]),(0,[z38,z0,z2,z3,z4,z184,z6]),(0,[z297,z0,z2,z3,z4,z24,z6]),(0,[z0,z2,z3,z4,z452,z5,z6]),(0,[z0,z2,z3,z616,z4,z5,z6])],[(0,[z617,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z219,z5,z6]),(0,[z29,z0,z2,z3,z4,z202,z6]),(0,[z618,z0,z2,z3,z4,z5,z6]),(0,[z0,z619,z2,z3,z4,z5,z6]),(0,[z620,z0,z2,z3,z4,z5,z6])],[(0,[z84,z0,z2,z3,z4,z5,z60]),(0,[z39,z0,z2,z3,z4,z24,z6]),(1,[z0,z40,z249,z4,z5,z6]),(0,[z0,z174,z63,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z621,z6]),(0,[z0,z2,z13,z54,z3,z4,z6])],[(0,[z0,z383,z3,z4,z184,z5,z6]),(0,[z48,z0,z2,z135,z4,z5,z6]),(0,[z0,z2,z3,z622,z4,z5,z6]),(0,[z297,z0,z2,z99,z4,z5,z6]),(0,[z0,z2,z3,z4,z623,z91,z6]),(1,[z297,z0,z2,z4,z5,z21]),(0,[z0,z2,z3,z4,z8,z6,z139])],[(0,[z0,z2,z3,z624,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z625,z6]),(0,[z0,z2,z3,z4,z5,z6,z626])],[(0,[z39,z0,z2,z75,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z627,z6]),(0,[z0,z628,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z629,z6]),(0,[z0,z2,z630,z3,z4,z5,z6])]],
   [[(0,[z84,z0,z2,z3,z146,z5,z6]),(0,[z0,z2,z3,z4,z631,z5,z6]),(0,[z0,z2,z3,z4,z632,z5,z6]),(0,[z227,z0,z2,z3,z4,z24,z6]),(0,[z633,z0,z2,z3,z4,z5,z6]),(0,[z634,z0,z2,z3,z4,z5,z6]),(0,[z0,z635,z2,z3,z4,z5,z6]),(0,[z0,z2,z514,z3,z4,z5,z6]),(0,[z251,z0,z2,z3,z4,z5,z6])],[(0,[z124,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z249,z4,z8,z6]),(0,[z0,z2,z3,z4,z636,z5,z6]),(0,[z0,z2,z99,z3,z5,z82,z6]),(0,[z0,z637,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z72,z8,z6])],[(0,[z0,z2,z3,z280,z4,z24,z6]),(0,[z297,z0,z2,z3,z4,z26,z6]),(0,[z38,z0,z2,z3,z4,z26,z6]),(0,[z0,z2,z3,z4,z638,z5,z6]),(0,[z0,z2,z3,z4,z55,z8,z6]),(0,[z0,z2,z639,z3,z4,z5,z6])],[(0,[z103,z0,z40,z3,z4,z5,z6]),(0,[z38,z0,z62,z2,z3,z4,z6]),(0,[z640,z0,z2,z3,z4,z5,z6]),(0,[z38,z7,z0,z2,z3,z4,z6]),(0,[z48,z69,z2,z3,z4,z5,z6]),(0,[z0,z2,z641,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z72,z5,z28]),(0,[z0,z2,z642,z3,z4,z5,z6]),(0,[z0,z2,z514,z3,z4,z6,z127])],[(0,[z0,z643,z2,z3,z4,z5,z6]),(0,[z39,z0,z2,z3,z4,z26,z6]),(0,[z38,z39,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z644,z5,z6]),(0,[z0,z2,z645,z3,z4,z5,z6]),(0,[z0,z2,z27,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z5,z646,z6]),(0,[z38,z0,z2,z3,z25,z4,z6]),(0,[z0,z2,z3,z647,z4,z5,z6]),(1,[z0,z3,z4,z5,z6,z560])],[(0,[z0,z2,z3,z4,z5,z648,z6]),(1,[z0,z3,z562,z4,z5,z6]),(0,[z0,z2,z99,z3,z184,z5,z6]),(0,[z297,z0,z2,z3,z4,z5,z21])],[(0,[z0,z2,z3,z649,z4,z5,z6]),(0,[z0,z2,z3,z4,z208,z5,z6]),(0,[z0,z254,z2,z249,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z650,z6]),(0,[z0,z2,z99,z3,z25,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z651])],[(1,[z0,z2,z3,z4,z104,z6]),(0,[z0,z2,z3,z4,z4,z5,z6]),(0,[z0,z2,z3,z4,z26,z196,z6]),(1,[z38,z0,z2,z3,z4,z28]),(0,[z0,z2,z3,z5,z539,z196,z6])]],
   [[(0,[z0,z2,z3,z4,z146,z5,z6]),(0,[z0,z652,z2,z3,z4,z5,z6]),(0,[z0,z2,z85,z3,z4,z5,z6]),(0,[z41,z94,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z26,z8,z6]),(0,[z0,z2,z3,z4,z5,z121,z150]),(0,[z0,z2,z3,z4,z653,z5,z6]),(1,[z0,z63,z3,z64,z5,z6]),(0,[z38,z0,z63,z2,z3,z4,z6]),(0,[z0,z174,z2,z3,z4,z8,z6])],[(0,[z0,z2,z3,z4,z5,z654,z6]),(0,[z0,z2,z105,z4,z5,z6,z21]),(1,[z227,z0,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z6,z655]),(0,[z0,z2,z147,z25,z4,z5,z6])],[(0,[z0,z2,z51,z3,z15,z5,z6]),(0,[z0,z2,z3,z280,z4,z26,z6]),(1,[z0,z342,z3,z4,z5,z6]),(0,[z48,z0,z2,z3,z4,z248,z6]),(0,[z0,z656,z2,z3,z4,z5,z6]),(0,[z0,z2,z657,z3,z4,z5,z6]),(0,[z0,z2,z658,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z659,z5,z6]),(1,[z0,z2,z3,z4,z271,z6])],[(0,[z0,z2,z3,z660,z4,z5,z6]),(1,[z0,z2,z3,z4,z623,z6]),(0,[z0,z2,z3,z661,z4,z5,z6]),(1,[z106,z0,z2,z3,z5,z127])],[(1,[z0,z2,z3,z172,z5,z6]),(1,[z37,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z405,z6]),(0,[z0,z2,z3,z4,z662,z5,z6]),(0,[z0,z2,z13,z3,z4,z183,z6])],[(1,[z0,z2,z3,z4,z409,z6]),(0,[z663,z0,z2,z3,z4,z5,z6]),(0,[z22,z0,z2,z3,z4,z24,z6]),(0,[z29,z0,z2,z3,z4,z24,z6]),(0,[z0,z2,z3,z4,z664,z5,z6]),(0,[z38,z0,z2,z13,z3,z4,z6]),(0,[z0,z2,z665,z3,z4,z5,z6])],[(0,[z7,z0,z2,z105,z4,z5,z6]),(0,[z0,z2,z3,z184,z64,z5,z6]),(0,[z0,z2,z3,z4,z179,z5,z24]),(0,[z0,z2,z3,z666,z4,z5,z6]),(0,[z0,z2,z3,z4,z26,z82,z6]),(0,[z0,z2,z3,z4,z5,z667,z6])],[(0,[z0,z668,z2,z3,z4,z5,z6])]],
   [[(0,[z84,z0,z123,z3,z4,z5,z6]),(0,[z0,z2,z669,z3,z4,z5,z6]),(0,[z0,z2,z3,z52,z15,z5,z6]),(0,[z0,z2,z3,z4,z670,z5,z6]),(0,[z0,z671,z2,z3,z4,z5,z6]),(0,[z297,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z182]),(0,[z0,z2,z3,z183,z5,z14,z6]),(0,[z0,z672,z2,z3,z4,z5,z6]),(0,[z38,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z673])],[(0,[z674,z0,z2,z3,z4,z5,z6]),(0,[z39,z0,z2,z3,z4,z5,z6]),(0,[z0,z675,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z3,z4,z26,z6]),(0,[z0,z2,z3,z676,z4,z5,z6]),(0,[z0,z677,z2,z3,z4,z5,z6]),(0,[z0,z2,z509,z3,z4,z5,z6])],[(0,[z0,z2,z3,z678,z4,z5,z6]),(0,[z0,z2,z679,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z24,z377,z6]),(0,[z0,z2,z3,z4,z214,z5,z6]),(0,[z0,z2,z680,z3,z4,z5,z6]),(0,[z0,z2,z54,z3,z280,z4,z6]),(0,[z106,z0,z2,z3,z4,z5,z82]),(0,[z38,z0,z2,z3,z4,z6,z127]),(0,[z38,z620,z0,z2,z3,z4,z6]),(0,[z273,z0,z2,z3,z4,z8,z6])],[(0,[z103,z0,z2,z3,z4,z24,z6]),(0,[z0,z254,z2,z3,z4,z26,z6]),(0,[z0,z2,z3,z4,z5,z681,z6])],[(0,[z0,z2,z27,z161,z4,z5,z6]),(0,[z0,z2,z682,z3,z4,z5,z6]),(0,[z22,z0,z2,z3,z4,z26,z6]),(0,[z29,z0,z2,z3,z4,z26,z6]),(0,[z0,z79,z2,z3,z4,z5,z6]),(0,[z683,z0,z2,z3,z4,z5,z6])],[(1,[z124,z2,z3,z184,z5,z6]),(0,[z38,z0,z2,z3,z4,z57,z6]),(0,[z0,z2,z3,z4,z623,z5,z6])],[(0,[z191,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z5,z684,z6])]],
   [[(0,[z0,z2,z2,z3,z4,z5,z6]),(0,[z0,z2,z105,z25,z4,z5,z6]),(1,[z0,z2,z3,z4,z6,z439]),(0,[z0,z2,z3,z685,z4,z5,z6]),(0,[z0,z2,z3,z280,z4,z5,z6])],[(0,[z686,z0,z2,z3,z4,z5,z6]),(0,[z0,z63,z3,z4,z64,z5,z6]),(0,[z191,z0,z2,z3,z4,z5,z28]),(0,[z687,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z173,z184,z5,z6]),(1,[z0,z2,z3,z4,z309,z6]),(0,[z0,z2,z3,z688,z4,z5,z6]),(0,[z0,z689,z2,z3,z4,z5,z6]),(0,[z38,z0,z320,z2,z3,z4,z6]),(0,[z494,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z99,z4,z91,z5,z6]),(1,[z0,z2,z469,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z6,z690]),(0,[z0,z2,z13,z3,z4,z8,z6]),(0,[z327,z0,z2,z3,z4,z5,z6])],[(0,[z39,z0,z2,z3,z4,z178,z6]),(0,[z0,z2,z3,z25,z4,z24,z6]),(0,[z0,z2,z3,z108,z4,z5,z6]),(0,[z0,z2,z691,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z692]),(0,[z0,z79,z2,z3,z4,z6,z28]),(0,[z0,z2,z3,z4,z693,z5,z6]),(0,[z0,z694,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z695]),(0,[z0,z696,z2,z3,z4,z5,z6])],[(0,[z48,z38,z0,z2,z3,z4,z6]),(1,[z0,z2,z3,z4,z444,z6]),(0,[z0,z2,z3,z4,z697,z5,z6]),(0,[z0,z2,z3,z4,z5,z698,z6]),(0,[z0,z2,z3,z4,z78,z5,z6])],[(0,[z699,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z700,z5,z6]),(0,[z0,z63,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z701,z5,z6]),(0,[z0,z320,z2,z3,z4,z57,z6]),(1,[z191,z0,z3,z4,z5,z28]),(0,[z0,z2,z702,z3,z4,z5,z6])],[(0,[z0,z2,z3,z703,z4,z5,z6]),(0,[z48,z0,z2,z3,z419,z5,z6]),(0,[z48,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z704,z5,z6]),(0,[z0,z2,z147,z3,z280,z4,z6]),(0,[z478,z38,z0,z2,z3,z4,z6])],[(0,[z0,z85,z3,z161,z4,z5,z6]),(0,[z2,z3,z15,z4,z184,z5,z6]),(0,[z0,z2,z3,z4,z24,z408,z6]),(0,[z0,z2,z3,z4,z705,z5,z6]),(0,[z0,z706,z2,z3,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z38,z0,z62,z3,z4,z28]),(0,[z0,z2,z4,z24,z707,z6]),(0,[z37,z0,z708,z3,z4,z6]),(0,[z0,z79,z31,z3,z4,z6]),(0,[z0,z43,z3,z4,z221,z6]),(1,[z0,z2,z3,z4,z709])],[(0,[z0,z2,z263,z4,z8,z6]),(0,[z38,z0,z2,z3,z108,z6]),(0,[z0,z2,z3,z4,z710,z6])],[(0,[z227,z0,z711,z3,z4,z24])],[(0,[z0,z2,z3,z4,z712,z6]),(0,[z0,z3,z4,z24,z713,z6]),(0,[z0,z2,z3,z4,z714,z6]),(0,[z0,z40,z249,z4,z5,z6])],[(0,[z0,z2,z715,z4,z5,z6]),(0,[z0,z2,z3,z4,z716,z60]),(0,[z106,z0,z2,z3,z26,z127]),(0,[z0,z2,z3,z4,z5,z717]),(0,[z0,z718,z3,z4,z5,z6]),(0,[z0,z719,z3,z4,z5,z6]),(0,[z0,z2,z13,z3,z720,z6])],[(0,[z0,z721,z3,z4,z5,z6]),(0,[z37,z69,z2,z3,z4,z150]),(0,[z0,z2,z3,z4,z6,z722])],[(0,[z227,z0,z2,z3,z4,z196]),(0,[z38,z0,z63,z3,z64,z6]),(0,[z0,z2,z3,z4,z720,z6])],[(0,[z0,z2,z3,z4,z716,z6]),(0,[z124,z2,z3,z184,z24,z6]),(0,[z0,z2,z3,z4,z723,z6]),(0,[z38,z0,z2,z3,z4,z516]),(0,[z38,z0,z43,z3,z4,z8])],[(0,[z0,z2,z3,z724,z5,z6])],[(0,[z168,z85,z161,z4,z5,z6])],[(0,[z418,z0,z3,z4,z202,z6]),(0,[z0,z2,z3,z725,z5,z6]),(0,[z0,z2,z4,z5,z726,z6])],[(0,[z48,z2,z3,z4,z444,z49]),(0,[z0,z3,z4,z5,z6,z560])],[(0,[z727,z0,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z728,z6]),(0,[z0,z2,z3,z4,z179,z5]),(0,[z0,z2,z4,z26,z112,z6]),(0,[z0,z2,z3,z5,z6,z182])],[(0,[z0,z2,z3,z4,z5,z729]),(0,[z0,z3,z4,z5,z310,z28]),(0,[z0,z2,z99,z5,z35,z6]),(0,[z0,z3,z173,z5,z82,z324])],[(0,[z730,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z731]),(0,[z0,z252,z3,z4,z57,z6])],[(0,[z0,z2,z3,z4,z732,z6]),(0,[z7,z2,z105,z4,z232,z6]),(0,[z7,z144,z2,z3,z4,z6]),(0,[z124,z2,z3,z184,z26,z6]),(0,[z0,z733,z2,z3,z4,z6]),(0,[z418,z0,z3,z4,z247,z6]),(0,[z0,z63,z3,z64,z5,z6])]],
   [[(0,[z0,z2,z126,z4,z24,z6]),(0,[z2,z3,z4,z24,z6,z381]),(0,[z227,z0,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z6,z734]),(0,[z38,z0,z3,z52,z4,z28]),(0,[z0,z2,z13,z112,z14,z6]),(0,[z38,z0,z735,z3,z4,z6])],[(0,[z0,z2,z3,z4,z5,z736]),(0,[z38,z0,z2,z3,z4,z546]),(0,[z0,z2,z3,z4,z737,z6]),(0,[z0,z2,z738,z3,z4,z6])],[(0,[z0,z2,z3,z4,z739,z6]),(0,[z38,z0,z43,z3,z4,z121])],[(0,[z84,z123,z3,z4,z5,z60]),(0,[z29,z0,z3,z4,z202,z6]),(0,[z0,z2,z3,z4,z709,z139])],[(0,[z0,z2,z3,z4,z740,z6]),(0,[z0,z2,z3,z4,z741,z6])],[(0,[z0,z2,z3,z4,z742,z6]),(0,[z38,z472,z0,z2,z3,z4]),(0,[z38,z0,z2,z3,z4,z10]),(0,[z743,z0,z2,z3,z4,z6])],[(0,[z744,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z745,z6]),(0,[z746,z2,z3,z4,z5,z6]),(0,[z38,z0,z2,z317,z3,z6]),(0,[z0,z747,z3,z4,z5,z6])],[(0,[z84,z123,z3,z146,z5,z6]),(0,[z48,z38,z0,z2,z3,z108]),(0,[z38,z0,z2,z3,z4,z68]),(0,[z0,z2,z3,z4,z748,z6])],[(0,[z0,z2,z3,z4,z6,z749]),(0,[z48,z2,z3,z4,z24,z49]),(0,[z2,z3,z4,z24,z399,z6]),(0,[z0,z2,z126,z4,z26,z6]),(0,[z0,z2,z3,z4,z750,z6])],[(0,[z168,z2,z161,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z751]),(0,[z22,z227,z0,z2,z3,z4]),(0,[z0,z2,z268,z4,z24,z6]),(0,[z0,z2,z4,z752,z24,z6]),(0,[z29,z0,z3,z4,z753,z6]),(0,[z0,z2,z754,z4,z5,z6])],[(0,[z0,z2,z3,z4,z755,z6]),(0,[z38,z0,z2,z3,z4,z571]),(0,[z38,z0,z2,z3,z4,z567]),(0,[z29,z227,z0,z2,z3,z4]),(0,[z0,z222,z3,z4,z5,z6]),(0,[z0,z2,z3,z280,z720,z6]),(0,[z0,z2,z756,z4,z8,z6])],[(0,[z0,z3,z4,z757,z5,z6]),(0,[z0,z758,z3,z4,z26,z6]),(0,[z0,z2,z3,z759,z5,z6])],[(0,[z760,z0,z2,z3,z4,z104]),(0,[z48,z38,z0,z2,z3,z4])],[(0,[z48,z81,z3,z4,z5,z49]),(0,[z0,z3,z761,z4,z5,z6]),(0,[z297,z0,z2,z4,z439,z21]),(0,[z0,z2,z762,z3,z4,z6])],[(0,[z144,z2,z3,z161,z4,z6]),(0,[z48,z38,z0,z81,z3,z4])],[(0,[z0,z2,z3,z4,z232,z6]),(0,[z0,z2,z3,z4,z763,z6])]],
   [[(0,[z0,z85,z3,z4,z24,z6]),(0,[z48,z2,z3,z4,z26,z49]),(0,[z0,z2,z51,z764,z5,z6])],[(0,[z2,z105,z765,z4,z5,z6]),(0,[z0,z2,z3,z4,z309,z6]),(0,[z227,z0,z2,z3,z4,z14]),(0,[z0,z2,z3,z4,z5,z709])],[(0,[z0,z2,z3,z4,z245,z60]),(0,[z0,z2,z257,z3,z24,z6]),(0,[z29,z0,z3,z4,z6,z299]),(0,[z38,z0,z43,z3,z4,z310])],[(0,[z0,z2,z766,z4,z5,z6]),(0,[z0,z2,z257,z161,z5,z6]),(0,[z0,z2,z3,z5,z767,z6]),(0,[z0,z2,z223,z4,z5,z768])],[(0,[z0,z2,z3,z4,z769,z6]),(0,[z41,z2,z3,z4,z6,z330]),(0,[z0,z3,z4,z5,z121,z770]),(0,[z38,z0,z2,z3,z4,z591])],[(0,[z0,z2,z3,z4,z245,z6]),(0,[z48,z2,z3,z108,z5,z49])],[(0,[z0,z2,z3,z4,z771,z6]),(0,[z0,z2,z3,z146,z245,z6]),(0,[z0,z2,z772,z4,z5,z6]),(0,[z0,z2,z3,z4,z773,z6]),(0,[z144,z2,z3,z4,z184,z6]),(0,[z0,z2,z268,z108,z5,z6]),(0,[z0,z2,z3,z4,z774,z6]),(0,[z0,z2,z223,z4,z345,z53])],[(0,[z38,z0,z2,z3,z4,z98]),(0,[z0,z2,z3,z775,z8,z6])],[(0,[z0,z85,z3,z4,z26,z6]),(0,[z0,z347,z27,z4,z5,z6]),(0,[z38,z0,z2,z3,z4,z446]),(0,[z0,z2,z3,z4,z72,z709])],[(0,[z0,z708,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z776,z6]),(0,[z0,z777,z3,z4,z5,z6]),(0,[z0,z2,z3,z778,z5,z6])],[(0,[z0,z2,z3,z4,z779,z6]),(0,[z760,z103,z0,z2,z3,z4]),(0,[z0,z2,z257,z3,z26,z6])],[(0,[z0,z2,z3,z780,z5,z6]),(0,[z227,z0,z2,z147,z3,z4]),(0,[z0,z2,z3,z4,z781,z6])],[(0,[z0,z2,z586,z3,z224,z6]),(0,[z48,z38,z620,z2,z3,z4]),(0,[z38,z0,z2,z3,z782,z6])],[(0,[z227,z0,z2,z783,z3,z4]),(0,[z2,z3,z4,z140,z26,z6]),(0,[z297,z0,z2,z276,z4,z21]),(0,[z290,z0,z2,z56,z4,z6])],[(0,[z0,z2,z145,z4,z24,z6]),(0,[z0,z2,z3,z4,z784,z6]),(0,[z0,z2,z3,z4,z785,z6]),(0,[z0,z2,z3,z4,z786,z6]),(0,[z0,z42,z3,z4,z5,z28]),(0,[z0,z2,z147,z4,z196,z6]),(0,[z0,z2,z223,z4,z53,z8])],[(0,[z0,z2,z3,z4,z6,z787]),(0,[z0,z2,z3,z4,z788,z6]),(0,[z0,z2,z3,z4,z8,z435]),(0,[z0,z2,z509,z13,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z789,z6]),(0,[z227,z0,z63,z2,z3,z4]),(0,[z2,z153,z3,z4,z26,z6]),(0,[z0,z2,z25,z5,z6,z311]),(0,[z38,z0,z2,z3,z4,z133])],[(0,[z0,z2,z188,z4,z245,z6]),(0,[z0,z2,z145,z4,z73,z6])],[(0,[z0,z2,z790,z4,z5,z6]),(0,[z0,z2,z509,z4,z8,z6])],[(0,[z0,z2,z3,z4,z6,z791]),(0,[z48,z38,z69,z2,z3,z4]),(0,[z0,z2,z3,z4,z5,z792]),(0,[z0,z2,z3,z4,z793,z6])],[(0,[z227,z0,z2,z105,z3,z4]),(0,[z94,z2,z3,z4,z24,z6]),(0,[z0,z794,z3,z4,z26,z6]),(0,[z0,z79,z2,z3,z4,z6]),(0,[z38,z0,z2,z257,z3,z6])],[(0,[z0,z81,z3,z4,z5,z6]),(0,[z227,z0,z2,z3,z795,z4]),(0,[z0,z796,z2,z3,z4,z6])],[(0,[z0,z2,z145,z4,z26,z6]),(0,[z2,z797,z3,z4,z5,z6]),(0,[z0,z798,z2,z3,z4,z6])],[(0,[z0,z27,z565,z4,z5,z6]),(0,[z0,z2,z3,z4,z799,z6]),(0,[z227,z0,z2,z3,z4,z82]),(0,[z0,z2,z800,z4,z5,z6]),(0,[z0,z2,z3,z4,z801,z6])],[(0,[z38,z32,z0,z2,z3,z4])],[(0,[z0,z675,z3,z52,z5,z6]),(0,[z227,z0,z2,z3,z4,z68]),(0,[z0,z802,z3,z4,z5,z6]),(0,[z0,z291,z3,z4,z8,z6])],[(0,[z803,z0,z2,z3,z4,z6]),(0,[z2,z3,z765,z4,z5,z6]),(0,[z0,z2,z804,z4,z5,z6]),(0,[z2,z3,z4,z26,z805,z6])],[(0,[z0,z174,z3,z52,z24,z6]),(0,[z273,z227,z0,z2,z3,z4]),(0,[z0,z3,z4,z26,z6,z324])],[(0,[z0,z2,z3,z4,z806,z6]),(0,[z0,z2,z3,z4,z6,z807]),(0,[z0,z2,z75,z4,z178,z6])],[],[(0,[z227,z39,z0,z2,z3,z4]),(0,[z0,z2,z808,z4,z5,z6]),(0,[z94,z144,z2,z3,z4,z6]),(0,[z0,z2,z809,z4,z5,z6]),(0,[z0,z2,z147,z317,z4,z6])],[(0,[z37,z69,z0,z2,z3,z4]),(0,[z0,z2,z3,z4,z810,z6]),(0,[z0,z2,z3,z539,z8,z6]),(0,[z0,z2,z3,z4,z811,z6])]],
   [[(0,[z39,z2,z263,z15,z5,z6]),(0,[z0,z3,z4,z5,z6,z812]),(0,[z0,z2,z813,z4,z5,z6]),(0,[z38,z0,z2,z3,z4,z709])],[(0,[z38,z0,z2,z3,z4,z190]),(0,[z475,z2,z3,z4,z26,z6]),(0,[z106,z0,z2,z3,z158,z127])],[(0,[z0,z2,z3,z4,z814,z6]),(0,[z507,z0,z2,z4,z5,z21]),(0,[z227,z0,z212,z2,z3,z4]),(0,[z227,z0,z2,z3,z4,z53])],[(0,[z0,z2,z3,z4,z815,z236]),(0,[z0,z174,z3,z52,z26,z6]),(0,[z0,z2,z3,z4,z816,z6]),(0,[z0,z2,z3,z817,z8,z6])],[(0,[z0,z2,z188,z4,z26,z6]),(0,[z0,z2,z3,z4,z818,z6]),(0,[z0,z2,z263,z4,z24,z6])],[(0,[z0,z2,z161,z172,z5,z6]),(0,[z0,z711,z3,z4,z24,z6]),(0,[z0,z2,z99,z469,z3,z6])],[(0,[z0,z2,z3,z4,z24,z819]),(0,[z0,z2,z3,z4,z820,z6])],[(0,[z0,z27,z761,z4,z5,z6]),(0,[z0,z2,z317,z3,z5,z6])],[(0,[z0,z2,z3,z821,z5,z6]),(0,[z227,z0,z711,z2,z3,z4]),(0,[z0,z2,z3,z4,z822,z6])],[(0,[z0,z3,z4,z24,z6,z560]),(0,[z0,z1,z3,z4,z452,z6]),(0,[z48,z38,z0,z2,z3,z419]),(0,[z0,z2,z3,z4,z823,z6])],[(0,[z0,z2,z3,z824,z5,z6]),(0,[z38,z0,z347,z3,z4,z6])],[(0,[z103,z3,z438,z4,z5,z6]),(0,[z149,z0,z3,z4,z5,z28])],[(0,[z0,z2,z3,z312,z8,z6]),(0,[z0,z825,z2,z3,z4,z6])],[(0,[z0,z2,z826,z4,z5,z6]),(0,[z0,z383,z3,z4,z24,z6]),(0,[z0,z2,z3,z4,z363,z8]),(0,[z0,z43,z3,z4,z8,z6])],[(0,[z0,z2,z827,z4,z5,z6]),(0,[z2,z3,z4,z239,z26,z6])],[(0,[z0,z2,z3,z4,z5,z828]),(0,[z0,z2,z51,z25,z24,z6]),(0,[z0,z43,z3,z4,z5,z28])]],
   [[(0,[z0,z2,z3,z4,z829,z6]),(0,[z2,z3,z830,z4,z5,z6]),(0,[z69,z2,z3,z4,z95,z150]),(0,[z38,z0,z254,z27,z4,z6])],[(0,[z0,z2,z3,z831,z5,z6]),(0,[z832,z227,z0,z2,z3,z4]),(0,[z0,z2,z54,z4,z23,z6]),(0,[z38,z0,z2,z3,z4,z698]),(0,[z0,z3,z4,z8,z6,z833])],[(0,[z0,z2,z473,z25,z5,z6])],[(0,[z0,z2,z3,z4,z5,z834]),(0,[z227,z0,z2,z3,z4,z128]),(0,[z0,z2,z99,z469,z4,z6])],[(0,[z0,z2,z3,z4,z835,z6]),(0,[z0,z2,z836,z3,z4,z6])],[(0,[z0,z383,z3,z4,z26,z6]),(0,[z181,z2,z3,z4,z5,z49]),(0,[z0,z2,z3,z4,z194,z6]),(0,[z0,z43,z31,z3,z4,z6])],[(0,[z608,z2,z3,z4,z24,z6])],[(0,[z103,z464,z3,z4,z5,z6]),(0,[z227,z0,z144,z2,z3,z4]),(0,[z0,z2,z51,z25,z26,z6]),(0,[z0,z2,z3,z4,z837,z6]),(0,[z0,z2,z3,z183,z177,z6])],[(0,[z760,z0,z2,z3,z4,z5]),(0,[z38,z552,z0,z2,z3,z4]),(0,[z0,z2,z3,z4,z838,z6]),(0,[z0,z2,z3,z4,z5,z839]),(0,[z38,z0,z840,z3,z4,z6])],[(0,[z84,z123,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z841,z6]),(0,[z0,z2,z3,z4,z842,z6]),(0,[z0,z2,z4,z5,z6,z388]),(0,[z0,z2,z3,z4,z5,z843])],[(0,[z227,z0,z711,z3,z4,z5]),(0,[z0,z2,z3,z844,z5,z6]),(0,[z0,z2,z845,z3,z4,z6])],[(0,[z38,z0,z2,z3,z4,z256]),(0,[z38,z0,z2,z3,z846,z6])],[(0,[z0,z2,z3,z4,z847,z6]),(0,[z0,z2,z3,z4,z848,z6]),(0,[z0,z2,z3,z4,z333,z310]),(0,[z0,z849,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z850,z6]),(0,[z44,z0,z2,z4,z6,z283])],[(0,[z69,z2,z3,z4,z5,z150]),(0,[z0,z144,z2,z3,z4,z28])],[(0,[z38,z0,z2,z3,z4,z264]),(0,[z0,z2,z3,z4,z5,z851]),(0,[z0,z2,z852,z4,z5,z6])],[(0,[z0,z320,z31,z3,z4,z6])]],
   [[(0,[z0,z2,z3,z261,z129,z6]),(0,[z48,z0,z50,z2,z3,z4]),(0,[z853,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z236]),(0,[z0,z81,z268,z4,z5,z6]),(0,[z0,z2,z3,z4,z854,z6])],[(0,[z0,z2,z3,z146,z5,z236])],[(0,[z0,z2,z99,z313,z5,z6]),(0,[z39,z2,z3,z830,z5,z6]),(0,[z0,z2,z3,z855,z5,z6]),(0,[z38,z0,z2,z3,z759,z6])],[(0,[z227,z0,z2,z226,z3,z4]),(0,[z0,z2,z268,z4,z26,z6]),(0,[z0,z2,z3,z4,z856,z6])],[(0,[z84,z123,z188,z4,z5,z6]),(0,[z0,z857,z3,z4,z5,z6])],[(0,[z0,z2,z145,z4,z245,z6]),(0,[z0,z2,z3,z172,z208,z6]),(0,[z0,z858,z3,z4,z5,z6]),(0,[z0,z2,z859,z4,z5,z6]),(0,[z0,z2,z3,z4,z860,z24])],[(0,[z0,z2,z861,z4,z5,z6]),(0,[z37,z0,z2,z3,z4,z213]),(0,[z0,z40,z249,z4,z8,z6]),(0,[z0,z2,z862,z3,z4,z6])],[(0,[z0,z2,z863,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z864]),(0,[z38,z0,z342,z3,z4,z6]),(0,[z0,z2,z3,z4,z198,z6]),(0,[z38,z0,z2,z3,z4,z295]),(0,[z297,z0,z2,z4,z8,z21]),(0,[z0,z2,z509,z183,z5,z6])],[(0,[z0,z2,z3,z4,z865,z6]),(0,[z308,z2,z161,z4,z5,z6]),(0,[z38,z124,z2,z3,z184,z6]),(0,[z866,z0,z2,z3,z4,z24]),(0,[z867,z0,z2,z3,z4,z24]),(0,[z37,z0,z2,z3,z4,z121]),(0,[z0,z2,z3,z5,z82,z244])],[(0,[z0,z2,z13,z131,z3,z6]),(0,[z0,z2,z4,z5,z6,z768]),(0,[z38,z0,z2,z3,z4,z101])],[(0,[z0,z2,z868,z4,z5,z6]),(0,[z0,z2,z3,z108,z68,z6])],[(0,[z227,z191,z0,z2,z3,z4])],[(0,[z0,z2,z188,z4,z5,z236]),(0,[z0,z869,z3,z4,z5,z6]),(0,[z0,z2,z3,z26,z539,z6])],[(0,[z227,z0,z2,z3,z4,z183]),(0,[z0,z2,z3,z4,z870,z6])],[(0,[z38,z0,z2,z3,z4,z425]),(0,[z0,z2,z99,z147,z13,z6]),(0,[z0,z2,z3,z871,z8,z6])]],
   [[(0,[z227,z168,z0,z2,z3,z4]),(0,[z0,z63,z3,z697,z5,z6])],[(1,[z0,z2,z99,z469,z6]),(0,[z0,z2,z223,z4,z5,z53])],[(0,[z476,z62,z3,z4,z5,z6]),(0,[z0,z872,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z24,z435]),(0,[z48,z38,z0,z31,z3,z4]),(0,[z0,z2,z59,z4,z207,z6])],[(0,[z0,z2,z135,z4,z24,z6]),(0,[z0,z63,z3,z64,z8,z6]),(0,[z0,z2,z13,z3,z629,z6]),(0,[z0,z2,z147,z317,z3,z6])],[(0,[z191,z0,z79,z3,z4,z28]),(0,[z0,z2,z276,z3,z4,z6])],[(0,[z168,z2,z161,z4,z200,z6]),(0,[z0,z2,z3,z4,z873,z6]),(0,[z0,z604,z27,z4,z5,z6]),(0,[z594,z2,z3,z15,z5,z6]),(0,[z0,z874,z3,z4,z5,z6]),(0,[z0,z2,z875,z3,z4,z6]),(0,[z0,z342,z3,z419,z5,z6]),(0,[z0,z2,z876,z3,z5,z6])],[(0,[z84,z201,z3,z4,z5,z6]),(0,[z472,z0,z3,z4,z5,z28]),(0,[z227,z0,z62,z2,z3,z4]),(0,[z0,z3,z4,z5,z6,z877])],[(0,[z0,z2,z3,z172,z8,z6]),(0,[z0,z2,z878,z3,z4,z6])],[(0,[z0,z3,z4,z5,z6,z879]),(0,[z0,z2,z263,z4,z309,z6]),(0,[z0,z81,z135,z4,z5,z6]),(0,[z144,z2,z3,z4,z150,z6])],[(0,[z38,z0,z43,z3,z4,z6])],[(0,[z0,z2,z3,z4,z5,z880]),(0,[z0,z2,z3,z4,z5,z881]),(0,[z0,z2,z3,z4,z26,z435]),(0,[z0,z2,z3,z4,z6,z882]),(0,[z191,z0,z3,z4,z5,z770])],[(0,[z0,z2,z3,z4,z883,z6]),(0,[z0,z2,z135,z4,z26,z6]),(0,[z0,z2,z4,z5,z112,z6])],[(0,[z227,z0,z2,z3,z4,z884]),(0,[z0,z2,z3,z4,z5,z885]),(0,[z0,z886,z3,z4,z5,z6]),(0,[z297,z0,z2,z4,z5,z768]),(0,[z38,z0,z2,z3,z887,z6])],[(0,[z0,z2,z3,z4,z888,z6]),(0,[z227,z0,z174,z2,z3,z4]),(0,[z0,z2,z3,z889,z5,z6])],[(0,[z0,z2,z3,z4,z6,z709])],[(0,[z0,z890,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z891]),(0,[z892,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z893,z6]),(0,[z38,z0,z81,z3,z4,z6]),(0,[z38,z0,z894,z2,z3,z4]),(0,[z0,z2,z895,z3,z4,z6])]],
   [[(0,[z0,z2,z135,z108,z5,z6]),(0,[z0,z2,z25,z5,z348,z6])],[(0,[z896,z227,z0,z2,z3,z4])],[(0,[z227,z0,z783,z3,z4,z6]),(0,[z2,z3,z4,z150,z6,z330]),(0,[z0,z2,z3,z4,z897,z6])],[(0,[z227,z0,z2,z3,z4,z162])],[(0,[z0,z2,z3,z5,z6,z898]),(1,[z0,z3,z4,z5,z770])],[(0,[z0,z81,z3,z4,z248,z6]),(0,[z0,z2,z3,z4,z899,z6]),(0,[z0,z2,z3,z5,z6,z900]),(0,[z0,z2,z3,z4,z8,z709])],[(0,[z0,z2,z901,z4,z5,z6])],[(0,[z902,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z903,z6]),(0,[z2,z3,z830,z184,z5,z6]),(0,[z0,z61,z3,z4,z5,z121]),(0,[z0,z2,z4,z764,z5,z6])],[],[(0,[z0,z2,z13,z3,z224,z6])],[(0,[z0,z904,z2,z3,z4,z6])],[(0,[z227,z0,z2,z18,z3,z4]),(0,[z48,z38,z0,z342,z3,z4])],[(0,[z48,z38,z2,z3,z4,z49]),(0,[z0,z2,z3,z4,z905,z6]),(0,[z0,z906,z2,z3,z4,z6]),(0,[z0,z2,z4,z5,z768,z21]),(0,[z0,z2,z3,z4,z907,z6]),(0,[z0,z2,z3,z5,z82,z843])],[(0,[z0,z2,z3,z4,z908,z6]),(0,[z0,z2,z3,z24,z6,z182]),(0,[z0,z2,z3,z108,z248,z6]),(0,[z0,z2,z3,z280,z638,z6]),(0,[z273,z2,z3,z4,z6,z330])],[(0,[z2,z430,z3,z4,z24,z6]),(0,[z227,z0,z2,z3,z4,z23]),(0,[z38,z0,z2,z342,z3,z4]),(0,[z0,z320,z3,z4,z753,z6]),(0,[z297,z0,z2,z4,z5,z98])],[(0,[z0,z2,z3,z312,z24,z6]),(0,[z0,z2,z3,z4,z5,z909]),(0,[z0,z2,z263,z4,z26,z6]),(0,[z0,z2,z4,z5,z6,z910])]],
   [[(0,[z0,z3,z911,z4,z5,z6]),(0,[z39,z2,z3,z15,z8,z6]),(0,[z0,z2,z3,z5,z6,z912])],[(0,[z0,z2,z3,z4,z6,z913]),(0,[z0,z2,z914,z4,z5,z6])],[(0,[z0,z2,z3,z4,z915,z6]),(0,[z0,z2,z3,z4,z916,z6]),(0,[z48,z2,z3,z419,z5,z49])],[(0,[z0,z347,z3,z4,z5,z6]),(1,[z760,z0,z2,z3,z4]),(0,[z917,z0,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z918,z6]),(0,[z0,z2,z514,z4,z6,z388])],[(0,[z0,z2,z3,z4,z6,z919]),(0,[z0,z735,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z920,z6]),(0,[z267,z2,z3,z4,z24,z6]),(0,[z0,z2,z3,z4,z921,z6]),(0,[z38,z0,z708,z3,z4,z6])],[(0,[z0,z2,z3,z4,z5,z922]),(0,[z0,z2,z923,z3,z24,z6]),(0,[z924,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z925,z6])],[(0,[z0,z2,z75,z4,z8,z6]),(0,[z0,z926,z3,z4,z5,z6]),(0,[z227,z297,z0,z2,z3,z4]),(0,[z0,z927,z2,z3,z4,z6]),(0,[z0,z61,z3,z4,z5,z310]),(0,[z191,z0,z3,z4,z110,z28])],[(0,[z29,z0,z3,z4,z202,z435])],[(0,[z0,z81,z3,z4,z8,z6]),(0,[z0,z2,z509,z13,z14,z6])],[(0,[z0,z2,z3,z928,z5,z6]),(0,[z84,z123,z145,z4,z5,z6]),(0,[z442,z2,z161,z4,z5,z6]),(0,[z542,z2,z3,z15,z5,z6]),(0,[z227,z0,z61,z2,z3,z4]),(0,[z38,z69,z2,z3,z4,z150]),(0,[z0,z3,z4,z5,z650,z28])],[(0,[z0,z2,z3,z4,z929,z6]),(0,[z0,z63,z3,z4,z5,z60]),(0,[z0,z930,z3,z4,z24,z6]),(0,[z0,z2,z3,z4,z931,z6]),(1,[z0,z2,z4,z5,z768]),(0,[z0,z2,z800,z4,z8,z6])],[(0,[z0,z2,z3,z932,z5,z6]),(0,[z38,z0,z2,z808,z4,z6])],[(0,[z227,z0,z2,z3,z280,z4]),(0,[z0,z3,z4,z5,z6,z770]),(0,[z0,z2,z422,z4,z55,z6]),(0,[z0,z2,z3,z4,z933,z6])],[(0,[z0,z61,z3,z4,z221,z121]),(0,[z0,z2,z509,z280,z4,z6])],[(0,[z0,z347,z188,z4,z5,z6]),(0,[z0,z63,z3,z146,z5,z6]),(0,[z0,z2,z3,z4,z934,z6]),(0,[z0,z2,z3,z5,z6,z935]),(0,[z38,z0,z936,z3,z4,z6])]],
   [[(0,[z0,z2,z4,z937,z5,z6]),(0,[z0,z2,z938,z4,z5,z6]),(0,[z0,z2,z3,z183,z720,z6])],[(0,[z203,z2,z3,z4,z26,z6]),(0,[z0,z2,z3,z4,z72,z213]),(0,[z0,z2,z3,z108,z8,z6]),(0,[z0,z2,z3,z4,z939,z6]),(0,[z0,z2,z3,z173,z78,z82])],[(0,[z0,z2,z145,z4,z5,z236]),(0,[z227,z0,z2,z13,z3,z4]),(0,[z0,z61,z3,z4,z5,z33]),(0,[z0,z940,z2,z3,z4,z6])],[(0,[z0,z2,z3,z4,z5,z941]),(0,[z38,z0,z2,z263,z4,z6]),(0,[z0,z942,z2,z3,z4,z6]),(0,[z0,z61,z3,z4,z121,z8]),(0,[z0,z2,z4,z5,z823,z6]),(0,[z106,z0,z2,z126,z5,z6])],[(0,[z0,z2,z3,z943,z5,z6]),(0,[z0,z944,z3,z4,z5,z6]),(0,[z0,z2,z3,z24,z767,z6])],[(0,[z84,z227,z0,z2,z3,z4]),(0,[z0,z3,z4,z5,z945,z6]),(0,[z0,z2,z3,z4,z946,z6]),(0,[z0,z2,z13,z3,z288,z6])],[(0,[z0,z2,z3,z4,z6,z947]),(0,[z0,z81,z3,z4,z68,z6]),(0,[z0,z2,z3,z4,z948,z6]),(0,[z0,z2,z3,z289,z14,z6])],[(0,[z124,z2,z3,z830,z5,z6]),(0,[z502,z0,z2,z3,z4,z8]),(0,[z0,z2,z3,z4,z949,z6])],[(0,[z37,z620,z2,z3,z4,z6])],[(0,[z603,z2,z3,z4,z26,z6]),(0,[z0,z2,z3,z4,z950,z6])],[(0,[z38,z0,z2,z188,z4,z6]),(0,[z0,z2,z3,z419,z5,z6]),(0,[z41,z2,z3,z4,z26,z6]),(0,[z0,z3,z4,z5,z6,z324]),(0,[z106,z0,z2,z514,z3,z127])],[(0,[z7,z2,z105,z92,z5,z6]),(0,[z0,z2,z951,z3,z4,z6]),(0,[z297,z0,z2,z4,z24,z21]),(0,[z0,z2,z99,z91,z5,z6]),(0,[z38,z0,z31,z3,z4,z333])],[(0,[z84,z797,z3,z4,z5,z6]),(0,[z0,z2,z952,z4,z5,z6])],[],[(0,[z0,z2,z3,z5,z953,z6])],[(0,[z0,z2,z3,z4,z954,z6])]],
   [[(0,[z0,z2,z126,z15,z5,z6]),(0,[z227,z0,z2,z3,z4,z408]),(0,[z0,z2,z99,z659,z5,z6]),(0,[z0,z2,z257,z5,z53,z6])],[(0,[z0,z2,z3,z4,z955,z6]),(0,[z0,z2,z956,z3,z4,z6])],[(0,[z38,z0,z2,z497,z3,z4]),(0,[z0,z2,z957,z3,z4,z6]),(0,[z0,z2,z54,z4,z6,z283]),(0,[z38,z0,z2,z3,z4,z139])],[(0,[z227,z69,z0,z2,z3,z4]),(0,[z227,z0,z783,z3,z4,z24]),(0,[z297,z0,z2,z4,z26,z21])],[(0,[z0,z2,z3,z4,z958,z6]),(0,[z0,z959,z3,z4,z5,z6]),(0,[z38,z69,z0,z43,z3,z4]),(0,[z0,z2,z3,z4,z960,z6]),(0,[z0,z2,z13,z3,z659,z6]),(0,[z0,z2,z4,z5,z53,z768]),(0,[z0,z2,z3,z173,z5,z82]),(0,[z0,z2,z961,z4,z5,z6])],[(0,[z0,z2,z3,z4,z962,z6])],[(0,[z0,z63,z3,z64,z24,z6]),(0,[z963,z2,z3,z4,z5,z6])],[],[(0,[z0,z2,z964,z4,z5,z6]),(0,[z227,z0,z2,z3,z4,z184]),(0,[z0,z2,z509,z4,z24,z6]),(0,[z0,z965,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z345,z6])],[(0,[z0,z2,z3,z173,z5,z567]),(0,[z0,z2,z4,z24,z112,z6]),(0,[z0,z2,z3,z4,z110,z6])],[(0,[z0,z2,z3,z172,z24,z6]),(0,[z966,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z967]),(0,[z0,z2,z968,z3,z4,z6]),(0,[z0,z2,z3,z5,z843,z127])],[(0,[z0,z2,z3,z92,z5,z6]),(0,[z0,z969,z3,z4,z5,z6]),(0,[z970,z2,z3,z4,z5,z6])],[(0,[z2,z3,z4,z26,z367,z6]),(0,[z0,z2,z3,z280,z6,z301]),(0,[z0,z2,z3,z4,z971,z6])],[(0,[z84,z123,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z6,z972]),(0,[z0,z2,z3,z4,z973,z6]),(0,[z0,z747,z3,z4,z8,z6])],[(0,[z0,z2,z3,z974,z5,z6]),(0,[z0,z2,z3,z4,z860,z5]),(0,[z227,z0,z2,z3,z975,z4])],[(0,[z0,z976,z2,z3,z4,z6]),(0,[z227,z0,z2,z3,z161,z4]),(0,[z0,z2,z3,z4,z977,z6]),(0,[z0,z291,z3,z4,z24,z6])]],
   [[(0,[z168,z2,z161,z4,z8,z6]),(0,[z0,z2,z3,z4,z24,z751]),(0,[z0,z2,z509,z4,z26,z6]),(0,[z0,z2,z3,z4,z6,z978]),(1,[z0,z2,z509,z13,z6])],[(0,[z0,z2,z3,z4,z979,z6]),(0,[z866,z0,z2,z3,z4,z5]),(0,[z867,z0,z2,z3,z4,z5]),(0,[z0,z2,z3,z980,z5,z6]),(0,[z0,z2,z3,z4,z5,z981]),(0,[z0,z43,z3,z4,z202,z6]),(0,[z0,z222,z3,z4,z8,z6]),(0,[z38,z0,z31,z3,z4,z139])],[(0,[z982,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z172,z26,z6]),(0,[z0,z2,z983,z4,z5,z6]),(0,[z0,z254,z27,z4,z5,z6]),(0,[z0,z2,z3,z984,z5,z6]),(0,[z0,z174,z3,z844,z5,z6])],[(0,[z38,z0,z2,z3,z4,z236]),(0,[z0,z985,z3,z4,z5,z6]),(0,[z0,z2,z147,z539,z196,z6])],[(0,[z437,z2,z105,z4,z5,z6]),(0,[z227,z0,z2,z54,z3,z4]),(0,[z0,z2,z3,z4,z986,z6]),(0,[z0,z2,z147,z4,z405,z6]),(0,[z0,z2,z987,z3,z5,z6]),(0,[z0,z2,z988,z3,z4,z6]),(0,[z0,z2,z126,z514,z4,z6]),(0,[z38,z970,z2,z3,z4,z6])],[],[(0,[z0,z2,z989,z4,z5,z6]),(0,[z227,z94,z0,z2,z3,z4])],[(0,[z0,z291,z3,z4,z26,z6]),(0,[z0,z50,z2,z3,z4,z121])],[(0,[z37,z0,z794,z3,z4,z6]),(0,[z0,z3,z52,z844,z5,z6]),(0,[z0,z3,z4,z753,z5,z6]),(0,[z0,z144,z43,z3,z4,z6])],[(0,[z0,z3,z562,z4,z5,z6]),(0,[z0,z990,z3,z4,z5,z6]),(0,[z130,z2,z3,z4,z24,z6]),(0,[z0,z2,z3,z4,z6,z991]),(0,[z38,z0,z992,z3,z4,z6])],[(0,[z0,z2,z3,z4,z993,z6])],[(0,[z0,z2,z3,z4,z104,z6]),(0,[z0,z2,z3,z4,z6,z994])],[(0,[z227,z0,z2,z3,z4,z55])],[],[(0,[z0,z2,z3,z4,z5,z995]),(0,[z0,z123,z3,z4,z5,z60]),(0,[z0,z342,z3,z4,z5,z6]),(0,[z0,z2,z996,z4,z5,z6]),(0,[z0,z3,z4,z753,z57,z6])],[(0,[z0,z2,z3,z4,z6,z997]),(0,[z227,z2,z3,z4,z26,z24]),(0,[z0,z2,z3,z5,z720,z6])]],
   [[(0,[z37,z0,z2,z3,z4,z6]),(0,[z48,z227,z0,z2,z3,z4]),(0,[z227,z0,z2,z3,z4,z449]),(0,[z0,z2,z998,z3,z5,z6])],[(0,[z0,z2,z3,z4,z409,z6]),(0,[z0,z2,z4,z5,z6,z999]),(0,[z38,z0,z2,z3,z4,z396]),(0,[z0,z2,z514,z3,z4,z6])],[(0,[z0,z1000,z3,z4,z5,z6]),(0,[z0,z2,z1001,z3,z4,z6]),(0,[z0,z2,z3,z4,z1002,z6]),(0,[z0,z3,z4,z5,z6,z1003]),(0,[z0,z2,z3,z4,z1004,z6]),(0,[z38,z0,z3,z4,z6,z560])],[(0,[z39,z2,z3,z15,z24,z6]),(0,[z0,z43,z3,z4,z24,z6]),(0,[z0,z2,z3,z1005,z5,z6])],[(0,[z412,z2,z161,z4,z5,z6]),(0,[z0,z3,z4,z1006,z5,z6]),(0,[z0,z383,z3,z64,z5,z6]),(0,[z227,z0,z2,z3,z4,z91]),(0,[z227,z0,z2,z3,z4,z139]),(0,[z38,z69,z0,z2,z3,z4])],[(0,[z0,z2,z3,z312,z73,z6]),(0,[z103,z62,z3,z4,z104,z6]),(0,[z38,z0,z383,z3,z4,z6]),(0,[z69,z2,z3,z4,z5,z1007]),(0,[z0,z2,z3,z4,z1008,z6])],[(0,[z39,z2,z75,z15,z5,z6]),(0,[z0,z2,z268,z419,z5,z6]),(0,[z69,z2,z3,z4,z70,z150])],[(0,[z0,z2,z3,z4,z1009,z6]),(0,[z0,z2,z3,z4,z1010,z6]),(0,[z510,z0,z2,z3,z385,z6]),(0,[z327,z0,z2,z3,z6,z301])],[(0,[z0,z2,z3,z4,z1011,z6])],[(0,[z0,z40,z3,z4,z5,z60]),(0,[z0,z2,z3,z4,z1012,z5]),(0,[z297,z0,z2,z257,z5,z21])],[(0,[z0,z2,z3,z312,z26,z6]),(0,[z1013,z0,z2,z3,z4,z6]),(0,[z0,z2,z1014,z3,z5,z6]),(0,[z0,z2,z75,z4,z24,z6]),(0,[z0,z2,z4,z24,z6,z388]),(0,[z0,z2,z18,z4,z196,z6]),(0,[z0,z2,z3,z4,z1015,z6])],[(0,[z103,z797,z3,z4,z5,z6]),(0,[z0,z43,z3,z4,z26,z6]),(0,[z0,z2,z3,z4,z1016,z6]),(0,[z0,z2,z3,z4,z1017,z6]),(0,[z0,z2,z469,z25,z4,z6]),(0,[z0,z2,z3,z4,z1018,z6]),(0,[z0,z2,z54,z4,z823,z6]),(0,[z0,z2,z3,z4,z72,z8])],[(0,[z0,z2,z3,z5,z539,z6]),(0,[z0,z2,z3,z4,z6,z439])],[(0,[z0,z2,z4,z5,z6,z1019])],[],[(0,[z0,z2,z3,z4,z805,z6]),(0,[z2,z3,z4,z805,z5,z6]),(0,[z0,z342,z3,z4,z5,z150]),(0,[z502,z0,z3,z4,z5,z28]),(0,[z38,z0,z2,z3,z4,z333]),(0,[z38,z0,z43,z3,z4,z28]),(0,[z37,z0,z31,z3,z4,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z1020]),(0,[z38,z0,z123,z3,z4,z28]),(0,[z0,z2,z1021,z3,z5,z6])],[(0,[z0,z2,z3,z1022,z5,z6]),(0,[z191,z0,z3,z4,z5,z28]),(0,[z0,z2,z3,z4,z1023,z6]),(0,[z0,z2,z51,z5,z477,z6]),(0,[z0,z2,z4,z6,z158,z388])],[(0,[z0,z2,z3,z4,z1024,z6]),(0,[z0,z2,z3,z4,z1025,z6]),(0,[z38,z0,z174,z3,z52,z6]),(0,[z0,z2,z99,z615,z5,z6])],[(0,[z124,z3,z562,z184,z5,z6]),(1,[z2,z3,z4,z805,z6]),(0,[z143,z2,z3,z4,z24,z6])],[(0,[z0,z1026,z3,z4,z5,z6]),(0,[z0,z2,z263,z15,z5,z6]),(0,[z0,z2,z3,z4,z5,z1027]),(0,[z0,z2,z3,z108,z24,z6]),(0,[z48,z38,z144,z2,z3,z4]),(0,[z297,z0,z2,z257,z5,z6])],[(0,[z0,z2,z3,z4,z815,z6]),(0,[z0,z2,z3,z1028,z5,z6]),(0,[z0,z3,z4,z221,z57,z6]),(0,[z0,z2,z147,z317,z196,z6]),(0,[z0,z2,z809,z4,z8,z6])],[(0,[z230,z2,z105,z4,z5,z6]),(0,[z1029,z227,z0,z2,z3,z4]),(1,[z0,z2,z3,z720,z6])],[(0,[z38,z69,z0,z31,z3,z4]),(0,[z38,z0,z40,z3,z4,z28]),(0,[z0,z2,z3,z4,z1030,z6]),(0,[z0,z31,z3,z4,z5,z6])],[(0,[z0,z40,z188,z4,z5,z6]),(0,[z0,z3,z4,z24,z6,z324]),(0,[z0,z2,z3,z4,z179,z95])],[(0,[z38,z0,z2,z3,z6,z182])],[(0,[z0,z2,z3,z4,z1031,z6])],[(0,[z0,z1032,z3,z4,z5,z6])],[(0,[z0,z2,z3,z172,z232,z6]),(0,[z0,z2,z3,z782,z5,z6]),(0,[z227,z0,z2,z3,z4,z95]),(0,[z227,z0,z2,z3,z4,z57]),(0,[z0,z2,z3,z108,z26,z6]),(0,[z303,z0,z43,z3,z4,z6])],[(0,[z0,z40,z249,z4,z24,z6]),(0,[z0,z2,z135,z419,z5,z6]),(0,[z0,z2,z1033,z4,z5,z6]),(0,[z0,z61,z3,z4,z5,z770])],[(0,[z0,z2,z3,z4,z5,z1034]),(0,[z0,z2,z317,z3,z8,z6])],[(0,[z0,z2,z3,z4,z5,z310])]],
   [[(0,[z0,z2,z3,z4,z78,z6])],[(0,[z124,z2,z3,z184,z219,z6]),(0,[z38,z0,z342,z3,z4,z5])],[(0,[z0,z2,z3,z4,z1035,z6]),(0,[z199,z2,z3,z4,z24,z6]),(0,[z0,z2,z1036,z3,z5,z6])],[(0,[z7,z2,z105,z4,z5,z6]),(0,[z0,z2,z4,z26,z1037,z6]),(0,[z0,z3,z844,z64,z5,z6]),(0,[z38,z0,z2,z3,z4,z8])],[(0,[z0,z2,z314,z4,z55,z6]),(0,[z0,z2,z1038,z4,z5,z6]),(0,[z0,z2,z1039,z3,z4,z6])],[(0,[z0,z2,z1040,z4,z5,z6]),(0,[z0,z2,z3,z4,z1041,z6]),(0,[z0,z40,z249,z4,z26,z6]),(0,[z0,z2,z3,z4,z57,z310]),(0,[z0,z2,z914,z4,z8,z6])],[(0,[z0,z27,z4,z5,z6,z569]),(0,[z0,z2,z3,z4,z221,z121]),(0,[z0,z2,z3,z764,z5,z6])],[(0,[z0,z2,z4,z8,z6,z1042])],[(0,[z286,z2,z3,z184,z5,z6]),(0,[z0,z1043,z3,z4,z5,z6]),(0,[z574,z2,z3,z15,z5,z6]),(0,[z0,z2,z1044,z4,z5,z6])],[(0,[z0,z2,z3,z4,z1045,z6]),(0,[z1046,z227,z0,z2,z3,z4]),(0,[z48,z342,z3,z4,z5,z49]),(0,[z0,z2,z3,z4,z1047,z6]),(0,[z0,z2,z147,z540,z4,z6]),(0,[z38,z0,z2,z998,z3,z6])],[(0,[z272,z38,z0,z2,z3,z4]),(0,[z0,z2,z3,z419,z248,z6])],[(0,[z84,z123,z3,z312,z5,z6]),(0,[z0,z2,z3,z4,z24,z736]),(0,[z0,z2,z3,z4,z6,z1048])],[(0,[z0,z2,z3,z4,z1049,z6]),(0,[z307,z38,z0,z2,z3,z4]),(0,[z38,z0,z2,z3,z4,z213]),(0,[z48,z2,z3,z4,z5,z1007]),(0,[z0,z1050,z3,z4,z5,z6]),(0,[z38,z251,z0,z2,z3,z4])],[],[(0,[z84,z38,z123,z3,z4,z6]),(1,[z0,z761,z4,z5,z6]),(0,[z38,z0,z2,z3,z4,z121])],[(0,[z0,z2,z3,z4,z6,z1051]),(0,[z69,z2,z3,z4,z214,z150]),(0,[z0,z2,z3,z4,z1052,z6]),(0,[z0,z2,z3,z4,z6,z1053]),(0,[z0,z2,z3,z4,z1054,z6]),(0,[z0,z2,z3,z4,z1055,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z60]),(0,[z0,z2,z3,z4,z26,z731]),(0,[z0,z2,z3,z4,z1056,z6]),(0,[z0,z291,z223,z4,z5,z53])],[(0,[z0,z2,z3,z146,z5,z60]),(0,[z0,z63,z3,z64,z26,z6]),(0,[z0,z2,z3,z289,z545,z6])],[(0,[z38,z0,z31,z3,z4,z8])],[(0,[z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z312,z5,z236]),(0,[z168,z2,z161,z4,z24,z6]),(0,[z574,z2,z105,z4,z5,z6])],[(0,[z0,z2,z3,z146,z5,z6]),(0,[z0,z2,z3,z1057,z5,z6]),(0,[z0,z222,z3,z4,z24,z6]),(0,[z69,z2,z3,z4,z8,z150])],[(0,[z0,z2,z470,z4,z405,z6])],[(0,[z0,z2,z3,z4,z6,z158]),(0,[z106,z0,z2,z126,z5,z127])],[(0,[z0,z2,z3,z830,z5,z6]),(0,[z39,z2,z3,z15,z309,z6]),(0,[z0,z1058,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z8,z236]),(0,[z0,z2,z3,z4,z1059,z28]),(0,[z0,z2,z469,z51,z3,z6]),(0,[z1060,z0,z2,z3,z4,z6])],[(0,[z0,z1061,z3,z4,z5,z6]),(0,[z297,z0,z2,z5,z182,z21])],[(0,[z0,z2,z3,z312,z245,z6]),(0,[z543,z2,z3,z4,z24,z6]),(0,[z0,z3,z1062,z4,z5,z6]),(0,[z38,z0,z1063,z3,z4,z6])],[(0,[z0,z1064,z3,z4,z5,z6]),(0,[z168,z2,z161,z4,z26,z6]),(0,[z1065,z0,z2,z3,z4,z6]),(1,[z2,z3,z830,z5,z6]),(0,[z227,z0,z783,z3,z4,z5]),(0,[z0,z2,z3,z4,z1066,z6])],[(0,[z0,z2,z188,z4,z5,z60]),(0,[z0,z222,z3,z4,z26,z6])],[(0,[z103,z62,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z1067,z6]),(0,[z0,z2,z765,z4,z5,z6]),(0,[z0,z783,z3,z4,z5,z6]),(0,[z0,z3,z4,z757,z26,z6]),(0,[z38,z0,z31,z3,z4,z121])],[(0,[z0,z2,z75,z4,z309,z6]),(0,[z0,z2,z3,z419,z8,z6]),(0,[z38,z0,z2,z3,z4,z310])],[(0,[z0,z2,z188,z4,z5,z6]),(0,[z2,z3,z4,z26,z179,z24]),(0,[z0,z2,z3,z4,z24,z864]),(0,[z37,z227,z0,z2,z3,z4]),(0,[z0,z2,z1068,z4,z5,z6]),(0,[z0,z2,z99,z91,z8,z6])]],
   [[(0,[z0,z2,z3,z4,z1069,z6]),(0,[z0,z2,z188,z146,z5,z6]),(0,[z0,z2,z1070,z4,z5,z6]),(0,[z1071,z0,z2,z3,z4,z6]),(0,[z39,z144,z2,z3,z4,z6])],[(1,[z2,z765,z4,z5,z6]),(0,[z0,z2,z1072,z4,z5,z6]),(0,[z227,z0,z2,z3,z173,z4]),(0,[z0,z2,z3,z4,z179,z8]),(0,[z29,z0,z79,z3,z4,z6]),(0,[z0,z2,z257,z3,z6,z439]),(0,[z0,z3,z4,z5,z6,z833])],[(0,[z103,z62,z3,z4,z167,z6]),(0,[z0,z2,z3,z4,z623,z6]),(0,[z106,z0,z2,z3,z5,z127])],[(0,[z0,z2,z3,z4,z1073,z6]),(1,[z48,z144,z2,z3,z4])],[],[(0,[z0,z2,z3,z4,z5,z1074]),(0,[z0,z2,z3,z4,z1075,z6]),(0,[z227,z0,z2,z3,z4,z8]),(0,[z0,z2,z3,z4,z1076,z6])],[(0,[z0,z2,z1077,z3,z4,z6]),(0,[z48,z50,z2,z3,z4,z49]),(0,[z1078,z0,z3,z4,z5,z6])],[(0,[z240,z2,z3,z4,z24,z6]),(0,[z251,z2,z3,z4,z95,z6])],[(0,[z38,z507,z0,z2,z3,z4]),(0,[z0,z1079,z3,z4,z5,z6]),(0,[z0,z2,z223,z4,z24,z53]),(0,[z0,z2,z3,z67,z449,z6])],[(0,[z38,z0,z2,z3,z4,z33])],[(0,[z0,z2,z3,z4,z1080,z6]),(0,[z0,z2,z3,z5,z6,z1081]),(0,[z0,z2,z3,z4,z219,z6]),(0,[z227,z0,z40,z2,z3,z4])],[(0,[z0,z2,z3,z419,z68,z6]),(0,[z0,z2,z3,z4,z1082,z6]),(0,[z38,z0,z2,z3,z4,z46])],[(0,[z0,z2,z1083,z3,z4,z6]),(0,[z0,z761,z249,z4,z5,z6]),(0,[z0,z874,z3,z4,z8,z6])],[(0,[z1084,z0,z2,z3,z4,z6]),(0,[z124,z2,z3,z184,z5,z6]),(0,[z0,z2,z51,z703,z5,z6]),(0,[z38,z0,z2,z75,z4,z6]),(0,[z227,z0,z2,z3,z4,z179]),(0,[z0,z2,z3,z4,z72,z110])],[(0,[z1085,z0,z2,z3,z4,z6]),(0,[z0,z1086,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z1087,z6]),(0,[z0,z81,z3,z4,z24,z6]),(0,[z0,z2,z4,z5,z1037,z6]),(1,[z38,z0,z342,z3,z4]),(0,[z38,z0,z40,z249,z4,z6])]],
   [[(0,[z227,z0,z2,z3,z4,z121]),(1,[z0,z3,z4,z753,z6]),(0,[z0,z2,z509,z13,z3,z6])],[(1,[z227,z0,z2,z3,z4]),(0,[z0,z1088,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z1089,z6])],[(0,[z48,z2,z3,z4,z6,z330]),(0,[z0,z2,z3,z4,z1090,z6]),(0,[z38,z0,z2,z3,z173,z82])],[(0,[z0,z2,z3,z4,z1091,z6]),(0,[z0,z2,z3,z4,z5,z1092])],[(0,[z0,z2,z3,z4,z1093,z6]),(0,[z37,z0,z2,z3,z4,z215])],[(0,[z0,z2,z75,z4,z26,z6]),(0,[z0,z2,z3,z1094,z5,z6]),(0,[z0,z2,z3,z980,z8,z6])],[(0,[z94,z2,z3,z4,z805,z6]),(0,[z0,z3,z4,z24,z945,z6]),(0,[z0,z2,z3,z4,z1095,z6]),(0,[z0,z254,z27,z4,z8,z6]),(0,[z0,z2,z126,z4,z5,z6]),(0,[z0,z2,z3,z4,z6,z1096]),(0,[z38,z106,z0,z2,z3,z127])],[(0,[z0,z81,z3,z4,z26,z6])],[(0,[z0,z2,z3,z4,z213,z150]),(0,[z0,z2,z3,z846,z5,z6])],[(0,[z0,z61,z3,z4,z5,z448]),(0,[z0,z758,z3,z4,z5,z6]),(0,[z227,z0,z2,z3,z25,z4]),(0,[z0,z1097,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z8,z596]),(0,[z0,z2,z3,z4,z1098,z6]),(0,[z0,z2,z126,z4,z6,z158]),(0,[z38,z0,z222,z3,z4,z6])],[],[(0,[z0,z2,z3,z4,z1099,z6])],[(0,[z0,z2,z1100,z4,z5,z6]),(0,[z0,z81,z3,z108,z5,z6])],[(0,[z0,z2,z1101,z3,z4,z6]),(0,[z38,z0,z2,z827,z4,z6]),(0,[z0,z2,z4,z8,z6,z1102])],[(0,[z0,z50,z2,z3,z4,z6]),(0,[z144,z2,z3,z4,z26,z6]),(0,[z48,z2,z3,z4,z5,z49]),(0,[z106,z0,z2,z3,z5,z98]),(0,[z0,z2,z4,z55,z823,z6]),(0,[z0,z2,z509,z13,z4,z6])],[(0,[z0,z2,z3,z4,z1103,z6]),(0,[z0,z2,z3,z4,z1104,z6])]],
   [[(0,[z0,z3,z4,z5,z6,z1105])],[(0,[z38,z168,z2,z161,z4,z6]),(0,[z0,z2,z317,z3,z24,z6]),(1,[z0,z2,z4,z823,z6])],[(0,[z227,z94,z2,z3,z4,z24]),(0,[z0,z2,z3,z821,z24,z6])],[(0,[z80,z2,z3,z4,z26,z6]),(0,[z478,z0,z31,z3,z4,z6])],[],[(0,[z38,z0,z2,z135,z4,z6]),(0,[z0,z2,z3,z4,z1106,z6]),(0,[z0,z2,z54,z4,z55,z6])],[(0,[z0,z85,z3,z4,z5,z6]),(0,[z37,z0,z2,z3,z4,z28])],[(0,[z2,z180,z3,z4,z26,z6]),(0,[z38,z0,z2,z3,z4,z157]),(0,[z0,z1107,z3,z4,z5,z6])],[(0,[z0,z2,z257,z3,z5,z6]),(0,[z0,z2,z3,z4,z1108,z6])],[(0,[z0,z2,z3,z4,z95,z6]),(0,[z0,z2,z317,z3,z26,z6]),(0,[z0,z2,z1109,z3,z4,z6]),(1,[z0,z2,z3,z5,z843])],[(0,[z0,z2,z3,z4,z1110,z6]),(0,[z0,z2,z3,z4,z1111,z6]),(0,[z0,z347,z3,z4,z8,z6]),(0,[z124,z383,z3,z184,z5,z6]),(0,[z69,z0,z144,z2,z3,z4]),(0,[z0,z2,z3,z4,z1112,z6]),(0,[z0,z2,z3,z1113,z5,z6])],[(0,[z0,z3,z4,z5,z6,z1114])],[(0,[z0,z2,z3,z4,z1115,z6])],[(0,[z552,z0,z2,z3,z5,z127]),(0,[z0,z2,z3,z4,z1116,z6]),(0,[z0,z2,z1117,z3,z4,z6]),(0,[z0,z342,z268,z4,z5,z6])],[(0,[z38,z0,z2,z3,z4,z296]),(0,[z38,z0,z2,z3,z4,z179]),(0,[z0,z2,z3,z4,z110,z435])],[(0,[z519,z2,z3,z4,z26,z6]),(0,[z0,z2,z3,z173,z82,z8]),(0,[z38,z0,z1058,z3,z4,z6])]],
   [[(0,[z0,z2,z1118,z4,z5,z6]),(0,[z0,z2,z3,z4,z329,z8])],[(0,[z0,z2,z145,z4,z5,z60]),(0,[z0,z2,z1119,z3,z4,z6]),(0,[z38,z0,z2,z691,z3,z4]),(0,[z69,z0,z894,z2,z3,z4])],[(0,[z0,z794,z3,z4,z5,z6])],[(0,[z84,z123,z3,z4,z24,z6]),(0,[z227,z0,z2,z102,z3,z4]),(0,[z0,z2,z3,z4,z371,z213]),(0,[z0,z894,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z1120,z6]),(0,[z181,z38,z0,z2,z3,z4])],[(0,[z0,z2,z145,z4,z5,z6]),(0,[z0,z2,z3,z1121,z5,z6])],[(0,[z0,z2,z145,z146,z5,z6]),(0,[z0,z2,z1122,z4,z5,z6]),(0,[z227,z0,z2,z3,z52,z4]),(0,[z0,z2,z3,z4,z5,z770]),(0,[z0,z2,z147,z536,z4,z6]),(0,[z0,z2,z147,z56,z4,z6]),(0,[z285,z144,z2,z3,z4,z6])],[(0,[z84,z123,z3,z4,z73,z6]),(0,[z321,z0,z3,z4,z163,z6]),(0,[z38,z0,z2,z3,z4,z468])],[(0,[z69,z2,z3,z4,z24,z150])],[(0,[z683,z2,z3,z184,z5,z6]),(0,[z2,z3,z4,z26,z24,z6]),(0,[z1123,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z8,z6,z1124])],[(0,[z0,z383,z3,z52,z5,z6]),(0,[z0,z2,z1125,z4,z5,z6]),(0,[z0,z2,z3,z1126,z5,z6]),(0,[z38,z0,z2,z4,z112,z6]),(0,[z38,z0,z985,z3,z4,z6])],[(0,[z38,z39,z2,z3,z15,z6]),(0,[z38,z0,z2,z3,z4,z166]),(0,[z504,z0,z2,z3,z4,z8])],[(0,[z0,z2,z3,z4,z167,z6]),(0,[z0,z2,z3,z4,z24,z236]),(0,[z84,z123,z3,z4,z26,z6]),(0,[z1127,z227,z0,z2,z3,z4]),(0,[z0,z3,z4,z8,z6,z560]),(0,[z38,z1128,z2,z3,z4,z6])],[(0,[z0,z2,z1129,z4,z5,z6])],[(0,[z0,z2,z3,z4,z1130,z6]),(0,[z0,z144,z2,z3,z4,z121]),(0,[z0,z2,z3,z4,z1131,z6])],[(0,[z0,z2,z3,z4,z73,z236]),(0,[z227,z0,z2,z1132,z3,z4])],[(0,[z0,z2,z3,z4,z178,z6]),(0,[z69,z2,z3,z4,z26,z150]),(0,[z270,z0,z2,z3,z4,z8])]],
   [[(1,[z227,z0,z783,z3,z4]),(0,[z0,z2,z3,z4,z6,z1133])],[(0,[z0,z2,z3,z92,z208,z6]),(0,[z227,z0,z2,z3,z4,z26]),(0,[z0,z174,z3,z52,z5,z6]),(0,[z0,z2,z3,z4,z1134,z6]),(0,[z0,z2,z3,z4,z1135,z6])],[(0,[z0,z2,z3,z4,z1136,z6]),(0,[z0,z2,z3,z1137,z5,z6]),(0,[z0,z2,z863,z3,z24,z6]),(0,[z0,z2,z1138,z3,z5,z6])],[(0,[z0,z62,z3,z4,z5,z60]),(0,[z0,z2,z3,z4,z26,z236]),(0,[z0,z2,z3,z4,z8,z310])],[(0,[z0,z2,z3,z4,z1139,z6]),(0,[z0,z2,z3,z26,z1140,z6]),(0,[z0,z342,z135,z4,z5,z6]),(0,[z0,z2,z99,z469,z5,z6]),(0,[z38,z0,z291,z3,z4,z6])],[(0,[z0,z2,z3,z1141,z5,z6]),(0,[z227,z0,z2,z3,z4,z150]),(0,[z0,z2,z868,z4,z24,z6]),(0,[z0,z2,z3,z4,z72,z70]),(0,[z0,z614,z3,z4,z5,z121]),(0,[z0,z2,z3,z4,z1142,z6]),(0,[z38,z0,z2,z3,z4,z593]),(0,[z29,z38,z0,z3,z4,z28]),(0,[z0,z2,z3,z4,z8,z695])],[],[(0,[z0,z869,z3,z4,z24,z6]),(0,[z1143,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1144]),(0,[z0,z3,z52,z5,z6,z592]),(0,[z38,z0,z61,z3,z4,z121])],[(0,[z0,z2,z3,z4,z5,z1145]),(0,[z471,z2,z3,z4,z24,z6]),(0,[z38,z608,z0,z2,z3,z4])],[(0,[z1146,z0,z2,z3,z4,z236]),(0,[z0,z2,z3,z4,z1147,z6]),(0,[z0,z2,z3,z4,z1148,z6]),(0,[z0,z2,z126,z5,z82,z6])],[(0,[z0,z2,z3,z4,z213,z6]),(0,[z48,z2,z268,z4,z5,z49]),(0,[z0,z3,z4,z202,z753,z6]),(0,[z0,z2,z1149,z3,z4,z6]),(0,[z0,z2,z3,z173,z5,z843])],[(0,[z1150,z0,z2,z3,z4,z6]),(0,[z0,z2,z1151,z4,z5,z6]),(0,[z0,z711,z3,z4,z5,z6]),(0,[z0,z2,z1152,z3,z4,z6])],[(0,[z0,z2,z3,z4,z5,z819]),(0,[z38,z0,z2,z3,z4,z553]),(0,[z0,z2,z3,z4,z1153,z6])],[(0,[z0,z2,z3,z24,z539,z6]),(0,[z0,z2,z3,z4,z221,z6]),(0,[z38,z0,z794,z3,z4,z6])],[(0,[z0,z2,z3,z5,z6,z1154]),(0,[z1155,z227,z0,z2,z3,z4]),(0,[z0,z708,z3,z4,z26,z6]),(0,[z0,z342,z3,z4,z72,z5])],[(0,[z0,z2,z3,z4,z200,z6])]],
   [[(0,[z0,z2,z1156,z4,z5,z6]),(0,[z620,z2,z3,z4,z26,z6])],[(0,[z0,z1157,z3,z4,z5,z6]),(0,[z277,z2,z3,z4,z24,z6]),(0,[z0,z342,z3,z4,z248,z6]),(0,[z48,z0,z144,z2,z3,z4]),(0,[z0,z3,z4,z8,z6,z1158])],[(0,[z38,z0,z2,z3,z4,z60]),(0,[z0,z2,z3,z92,z8,z6]),(0,[z227,z106,z0,z2,z3,z4]),(0,[z48,z38,z0,z2,z135,z4]),(0,[z0,z2,z99,z540,z5,z6]),(0,[z0,z2,z59,z4,z196,z6])],[(0,[z0,z383,z3,z4,z5,z6]),(0,[z0,z2,z223,z4,z26,z53]),(0,[z2,z298,z3,z4,z26,z6]),(0,[z0,z2,z3,z4,z1159,z6])],[(0,[z0,z383,z3,z146,z5,z6]),(0,[z0,z2,z3,z4,z8,z60]),(0,[z0,z2,z3,z4,z24,z881]),(0,[z0,z2,z3,z4,z1160,z6]),(0,[z0,z2,z3,z4,z1161,z6]),(0,[z0,z2,z3,z385,z183,z6])],[(0,[z38,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z1162,z5,z6]),(0,[z0,z2,z105,z172,z5,z6]),(0,[z0,z2,z3,z1163,z5,z6]),(0,[z0,z2,z51,z25,z5,z6]),(0,[z0,z2,z1164,z3,z4,z6])],[(0,[z0,z2,z3,z4,z5,z1165]),(0,[z0,z2,z3,z4,z1166,z6]),(0,[z1167,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z1168,z6]),(0,[z0,z2,z4,z55,z195,z6])],[(0,[z0,z797,z3,z4,z5,z6]),(0,[z0,z2,z3,z1169,z5,z6]),(0,[z0,z2,z3,z4,z1170,z6]),(0,[z0,z1171,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z1172]),(0,[z48,z144,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z1173,z6])],[(0,[z7,z2,z765,z4,z5,z6]),(0,[z227,z0,z320,z2,z3,z4])],[(0,[z0,z2,z3,z4,z1174,z6]),(0,[z0,z2,z3,z4,z24,z891])],[(0,[z0,z2,z1175,z3,z4,z6]),(0,[z38,z0,z2,z4,z6,z388])],[(1,[z797,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z1176,z6]),(0,[z0,z2,z3,z4,z1177,z6])],[(0,[z559,z2,z3,z4,z26,z6])],[(0,[z20,z2,z3,z184,z5,z6]),(0,[z38,z0,z2,z3,z4,z70])],[(0,[z0,z3,z52,z4,z5,z60])],[(0,[z0,z2,z3,z4,z1178,z6])]],
   [[(0,[z0,z3,z562,z4,z8,z6])],[(0,[z0,z61,z3,z4,z24,z121]),(0,[z227,z0,z2,z51,z3,z4]),(0,[z48,z2,z135,z4,z5,z49]),(0,[z479,z0,z3,z4,z5,z28]),(0,[z38,z0,z3,z4,z6,z324])],[(0,[z0,z3,z52,z146,z5,z6]),(0,[z0,z2,z4,z752,z5,z6]),(0,[z0,z2,z268,z4,z5,z6]),(0,[z0,z2,z3,z4,z1179,z6]),(0,[z0,z2,z3,z4,z1180,z6])],[(0,[z0,z2,z3,z4,z1181,z104]),(0,[z0,z1182,z3,z4,z5,z6]),(0,[z0,z2,z99,z357,z5,z6])],[(0,[z0,z2,z3,z4,z1183,z6]),(0,[z38,z0,z3,z4,z57,z28]),(0,[z0,z2,z3,z4,z1184,z6]),(0,[z0,z2,z4,z5,z6,z1042]),(0,[z38,z0,z31,z3,z4,z6])],[(0,[z0,z342,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z1185,z6]),(0,[z38,z0,z2,z3,z4,z137]),(0,[z0,z1186,z3,z4,z5,z6])],[(0,[z227,z7,z0,z2,z3,z4]),(0,[z0,z2,z257,z105,z5,z6]),(0,[z0,z212,z3,z4,z408,z6]),(0,[z69,z2,z3,z4,z367,z5]),(0,[z0,z2,z1187,z4,z5,z6]),(0,[z38,z0,z2,z3,z539,z6]),(0,[z106,z0,z2,z3,z8,z127])],[],[(0,[z0,z2,z99,z370,z5,z6]),(0,[z38,z0,z2,z3,z4,z110])],[(0,[z0,z2,z3,z4,z24,z909]),(0,[z0,z61,z3,z4,z26,z121]),(0,[z0,z2,z3,z4,z1188,z6]),(0,[z0,z2,z3,z1189,z4,z6])],[(0,[z0,z2,z1190,z4,z5,z6]),(0,[z0,z2,z1191,z3,z4,z6]),(0,[z38,z0,z2,z3,z4,z530])],[(0,[z0,z2,z3,z4,z1192,z6]),(0,[z84,z123,z3,z4,z245,z6]),(0,[z2,z3,z15,z830,z5,z6]),(0,[z0,z2,z3,z4,z5,z1193])],[(0,[z227,z0,z2,z3,z4,z21]),(0,[z0,z2,z3,z4,z70,z6]),(0,[z0,z2,z1194,z4,z5,z6]),(0,[z38,z0,z1032,z3,z4,z6])],[(0,[z0,z347,z3,z4,z24,z6]),(0,[z227,z0,z2,z3,z15,z4]),(0,[z0,z2,z3,z887,z5,z6])],[(0,[z227,z0,z2,z99,z3,z4]),(0,[z48,z2,z3,z4,z248,z49]),(0,[z0,z2,z99,z469,z91,z6])],[(0,[z0,z2,z3,z4,z8,z171]),(0,[z106,z0,z2,z3,z5,z843]),(0,[z0,z2,z3,z5,z6,z843]),(0,[z0,z2,z3,z173,z271,z82])]],
   [[(0,[z0,z2,z3,z4,z6,z1195]),(0,[z0,z2,z99,z506,z5,z6])],[(0,[z124,z2,z3,z184,z8,z6]),(0,[z0,z2,z3,z4,z8,z627])],[(0,[z0,z2,z3,z1196,z5,z6]),(0,[z38,z0,z2,z3,z172,z6]),(0,[z2,z3,z4,z564,z24,z6]),(0,[z0,z342,z3,z4,z68,z6]),(0,[z0,z3,z844,z4,z5,z6]),(0,[z0,z43,z3,z4,z5,z121]),(0,[z0,z2,z147,z317,z5,z6])],[(0,[z0,z2,z3,z4,z245,z236]),(0,[z0,z2,z3,z4,z1197,z6]),(0,[z0,z2,z3,z4,z1198,z6]),(0,[z48,z38,z0,z2,z268,z4]),(0,[z0,z3,z4,z5,z770,z28])],[(0,[z0,z2,z3,z4,z6,z1199]),(0,[z0,z2,z3,z1200,z5,z6]),(0,[z0,z2,z3,z4,z202,z310])],[(0,[z0,z347,z3,z4,z26,z6]),(0,[z227,z0,z2,z3,z4,z64]),(0,[z321,z227,z0,z2,z3,z4]),(0,[z0,z2,z3,z261,z183,z6])],[(0,[z0,z2,z3,z1201,z5,z6]),(0,[z2,z3,z4,z805,z24,z6])],[(0,[z227,z0,z2,z3,z4,z6]),(0,[z273,z38,z0,z2,z3,z4])],[(0,[z0,z2,z3,z4,z5,z1202]),(0,[z0,z27,z3,z4,z5,z60]),(0,[z0,z3,z4,z5,z6,z1203]),(0,[z0,z2,z3,z4,z5,z435]),(0,[z191,z0,z3,z4,z8,z28])],[(0,[z0,z2,z3,z4,z5,z1204]),(0,[z0,z2,z135,z4,z5,z6]),(0,[z7,z2,z105,z4,z208,z6]),(0,[z0,z342,z3,z4,z5,z49]),(0,[z38,z0,z2,z3,z4,z206])],[(0,[z0,z2,z3,z4,z1205,z6]),(0,[z0,z2,z938,z4,z24,z6]),(0,[z0,z2,z314,z4,z339,z6]),(0,[z38,z0,z2,z1206,z4,z6])],[(0,[z0,z2,z3,z4,z24,z1027]),(0,[z0,z2,z3,z4,z179,z70]),(0,[z0,z2,z3,z4,z6,z1207])],[(0,[z523,z2,z3,z4,z24,z6]),(0,[z0,z2,z3,z4,z5,z1007])],[(0,[z0,z1097,z3,z4,z8,z6])],[(0,[z38,z0,z2,z145,z4,z6]),(0,[z0,z2,z3,z4,z1208,z6]),(0,[z0,z2,z1209,z3,z4,z6]),(0,[z0,z31,z3,z4,z8,z6])],[(0,[z0,z2,z3,z1210,z5,z6]),(0,[z0,z2,z223,z4,z5,z296]),(0,[z0,z2,z1211,z4,z5,z6]),(0,[z227,z0,z0,z2,z3,z4]),(0,[z227,z0,z2,z27,z3,z4]),(0,[z0,z2,z3,z8,z6,z182]),(0,[z0,z223,z4,z5,z53,z560])]],
   [[(1,[z2,z3,z4,z5,z1007]),(0,[z0,z2,z3,z4,z1212,z6])],[],[(0,[z48,z2,z3,z4,z8,z49]),(0,[z2,z3,z4,z5,z150,z1007]),(0,[z0,z43,z3,z4,z5,z310]),(0,[z0,z2,z3,z4,z533,z8]),(0,[z494,z0,z3,z4,z6,z299])],[(0,[z0,z1213,z3,z4,z5,z6]),(0,[z0,z2,z3,z1214,z5,z6]),(0,[z227,z0,z254,z2,z3,z4])],[(0,[z0,z2,z3,z419,z24,z6]),(0,[z227,z0,z2,z3,z249,z4]),(0,[z41,z2,z3,z4,z805,z6]),(0,[z0,z50,z2,z3,z4,z28])],[(0,[z0,z2,z99,z91,z24,z6]),(0,[z29,z0,z3,z4,z221,z6]),(0,[z38,z0,z3,z4,z121,z28])],[(0,[z0,z2,z3,z1215,z5,z6]),(0,[z0,z2,z3,z4,z248,z6]),(0,[z0,z2,z3,z4,z24,z310]),(0,[z0,z61,z3,z4,z194,z121]),(0,[z38,z1123,z2,z3,z4,z6])],[(0,[z0,z2,z1216,z4,z5,z6]),(0,[z38,z853,z2,z3,z4,z6])],[(0,[z0,z2,z3,z1217,z5,z6]),(0,[z0,z40,z761,z4,z5,z6]),(0,[z0,z2,z1218,z4,z5,z6]),(0,[z0,z3,z4,z5,z646,z28]),(0,[z0,z2,z1219,z3,z4,z6])],[(0,[z0,z81,z3,z419,z5,z6]),(1,[z0,z3,z844,z5,z6]),(1,[z0,z2,z147,z317,z6]),(0,[z0,z992,z3,z4,z5,z6])],[(0,[z0,z85,z3,z4,z8,z6]),(0,[z0,z2,z1220,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z1221]),(0,[z0,z79,z3,z4,z57,z6]),(0,[z1128,z2,z3,z4,z5,z6])],[(0,[z0,z2,z102,z3,z14,z6]),(0,[z2,z3,z4,z5,z1007,z49])],[(0,[z467,z2,z3,z4,z24,z6]),(0,[z0,z2,z3,z419,z26,z6]),(0,[z0,z2,z3,z4,z6,z1222]),(0,[z0,z3,z4,z26,z6,z560]),(0,[z38,z0,z2,z3,z4,z1059]),(0,[z0,z2,z3,z4,z1223,z6]),(0,[z0,z2,z4,z823,z196,z6]),(0,[z0,z2,z3,z4,z1224,z6]),(0,[z38,z0,z2,z126,z4,z6])],[(0,[z0,z2,z263,z4,z5,z6]),(0,[z0,z2,z99,z91,z26,z6])],[(0,[z0,z2,z3,z173,z24,z82]),(0,[z227,z0,z2,z3,z4,z72]),(0,[z0,z2,z257,z276,z3,z6])],[(0,[z38,z0,z2,z3,z4,z487]),(0,[z48,z2,z3,z4,z68,z49]),(0,[z0,z2,z3,z4,z6,z1225]),(0,[z0,z1226,z2,z3,z4,z6])]],
   [[(0,[z38,z0,z2,z3,z4,z448]),(0,[z0,z2,z126,z184,z5,z6]),(0,[z227,z0,z2,z3,z4,z163]),(0,[z0,z2,z1227,z4,z5,z6])],[(0,[z0,z2,z4,z5,z1228,z6])],[(0,[z0,z2,z3,z312,z5,z60]),(0,[z38,z0,z2,z268,z4,z6]),(0,[z38,z634,z0,z2,z3,z4])],[(0,[z0,z2,z3,z4,z1229,z6]),(0,[z0,z2,z317,z55,z5,z6])],[(0,[z0,z2,z102,z3,z162,z6]),(0,[z38,z227,z0,z2,z3,z4])],[(0,[z0,z2,z3,z92,z24,z6]),(0,[z0,z2,z3,z4,z214,z6]),(0,[z0,z2,z226,z4,z23,z6])],[(0,[z0,z2,z3,z1230,z5,z6]),(0,[z0,z2,z263,z4,z178,z6]),(0,[z0,z2,z3,z173,z26,z82]),(0,[z37,z144,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z1231,z6]),(0,[z0,z2,z3,z720,z14,z6]),(0,[z0,z2,z3,z4,z417,z8])],[(0,[z0,z2,z3,z4,z1232,z6])],[(0,[z227,z124,z0,z2,z3,z4]),(0,[z0,z2,z3,z4,z1233,z6])],[(0,[z168,z347,z161,z4,z5,z6]),(0,[z0,z2,z3,z4,z6,z1234])],[(0,[z0,z2,z3,z4,z8,z6]),(0,[z62,z797,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z1102])],[(0,[z0,z2,z3,z146,z8,z6]),(0,[z181,z123,z3,z4,z5,z6]),(0,[z0,z1235,z2,z3,z5,z6]),(0,[z0,z3,z4,z5,z6,z1236]),(0,[z0,z2,z3,z4,z1237,z6]),(0,[z0,z2,z3,z4,z5,z1238]),(0,[z2,z3,z4,z5,z6,z1239])],[(0,[z1240,z0,z2,z3,z4,z60]),(0,[z0,z2,z3,z1241,z5,z6]),(0,[z0,z254,z27,z4,z24,z6]),(0,[z0,z2,z3,z4,z26,z967]),(0,[z38,z0,z2,z3,z4,z299])],[(0,[z0,z2,z4,z5,z6,z1242]),(0,[z0,z2,z3,z92,z26,z6]),(0,[z2,z3,z4,z5,z6,z1243]),(0,[z38,z0,z2,z509,z4,z6])],[(0,[z168,z2,z765,z4,z5,z6]),(0,[z0,z212,z3,z4,z57,z6]),(0,[z0,z2,z13,z3,z14,z6])],[(0,[z0,z2,z3,z4,z1181,z5]),(0,[z0,z2,z1244,z4,z5,z6]),(0,[z0,z1245,z3,z4,z5,z6]),(0,[z2,z3,z661,z4,z24,z6]),(0,[z38,z0,z2,z3,z4,z305])]],
   [[(0,[z0,z2,z3,z1246,z5,z6]),(0,[z0,z2,z1247,z3,z4,z6]),(0,[z0,z2,z3,z4,z6,z1248]),(0,[z0,z2,z3,z280,z183,z6])],[(0,[z0,z930,z3,z4,z5,z6]),(0,[z0,z2,z25,z764,z5,z6])],[(0,[z0,z2,z3,z4,z6,z330]),(0,[z0,z2,z1249,z4,z5,z6]),(0,[z0,z63,z3,z844,z5,z6])],[(0,[z0,z3,z562,z4,z24,z6]),(0,[z2,z3,z4,z5,z6,z1007]),(0,[z0,z2,z3,z4,z5,z768])],[(0,[z103,z62,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z1250,z6]),(0,[z0,z2,z3,z4,z179,z24]),(0,[z0,z144,z2,z3,z4,z6]),(0,[z727,z0,z2,z3,z4,z24]),(0,[z0,z783,z3,z4,z24,z6]),(0,[z0,z254,z27,z4,z26,z6]),(0,[z0,z2,z983,z4,z26,z6])],[(0,[z0,z2,z3,z4,z1251,z6]),(0,[z1252,z0,z2,z3,z4,z6]),(0,[z0,z174,z3,z52,z8,z6]),(0,[z0,z2,z276,z3,z6,z182])],[(0,[z0,z2,z188,z4,z8,z6]),(0,[z1253,z0,z2,z3,z4,z6]),(0,[z0,z2,z756,z4,z5,z6])],[(0,[z84,z123,z3,z4,z5,z236]),(0,[z0,z2,z3,z4,z68,z6]),(0,[z38,z0,z27,z3,z4,z28]),(0,[z0,z2,z147,z4,z629,z6])],[(0,[z0,z2,z3,z4,z1254,z6]),(0,[z0,z1255,z3,z4,z5,z6]),(0,[z227,z0,z2,z3,z4,z24]),(0,[z0,z342,z3,z4,z24,z6]),(0,[z38,z297,z0,z2,z4,z21]),(0,[z0,z252,z3,z4,z333,z6])],[(0,[z0,z1256,z2,z3,z4,z6]),(0,[z106,z0,z2,z3,z24,z127]),(0,[z0,z2,z3,z280,z449,z6]),(0,[z38,z0,z2,z3,z4,z215]),(0,[z453,z0,z2,z3,z288,z6])],[(0,[z0,z347,z249,z4,z5,z6]),(0,[z38,z0,z85,z3,z4,z6]),(0,[z2,z3,z4,z24,z6,z330]),(0,[z0,z840,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z1257,z6]),(0,[z124,z2,z3,z184,z9,z6]),(0,[z0,z3,z562,z4,z26,z6]),(0,[z0,z2,z1258,z4,z5,z6])],[(0,[z0,z2,z1259,z4,z5,z6]),(0,[z227,z0,z2,z3,z67,z4]),(0,[z0,z2,z3,z4,z72,z68]),(0,[z29,z0,z3,z4,z202,z310])],[(0,[z0,z2,z3,z4,z1260,z6])],[(0,[z2,z3,z4,z95,z6,z330])],[(0,[z253,z0,z3,z4,z5,z28]),(0,[z0,z2,z3,z4,z5,z1261]),(0,[z0,z2,z761,z4,z5,z6])]],
   [[(0,[z7,z2,z105,z172,z5,z6]),(0,[z0,z342,z3,z4,z26,z6])],[(0,[z0,z2,z3,z1262,z5,z6]),(0,[z0,z2,z3,z4,z1263,z6]),(0,[z0,z2,z54,z4,z359,z6]),(0,[z297,z0,z2,z4,z5,z21]),(0,[z0,z2,z3,z6,z439,z182]),(0,[z0,z2,z1206,z4,z5,z6])],[(0,[z0,z2,z4,z5,z707,z6]),(0,[z0,z2,z268,z4,z248,z6]),(0,[z634,z2,z3,z4,z5,z150]),(0,[z38,z0,z2,z51,z25,z6]),(0,[z38,z0,z2,z1264,z4,z6]),(0,[z38,z0,z2,z961,z4,z6])],[(0,[z38,z0,z2,z3,z86,z4]),(0,[z0,z2,z3,z775,z5,z6]),(0,[z0,z2,z3,z5,z1140,z6]),(0,[z0,z2,z3,z4,z221,z28]),(0,[z0,z2,z317,z54,z3,z6]),(0,[z0,z144,z31,z3,z4,z6])],[],[(0,[z0,z2,z3,z4,z1265,z6]),(0,[z0,z3,z4,z5,z713,z6]),(0,[z38,z0,z2,z3,z92,z6]),(0,[z0,z342,z3,z108,z5,z6]),(0,[z0,z2,z3,z5,z6,z1124]),(0,[z0,z1086,z3,z4,z8,z6])],[(0,[z227,z227,z0,z2,z3,z4]),(0,[z0,z3,z4,z1006,z26,z6]),(0,[z38,z0,z43,z3,z4,z139])],[(0,[z0,z2,z3,z4,z1266,z6]),(0,[z0,z383,z3,z4,z8,z6]),(0,[z38,z0,z2,z223,z4,z53])],[(0,[z0,z2,z3,z4,z1267,z6]),(0,[z227,z0,z2,z3,z4,z377]),(0,[z0,z2,z3,z4,z1268,z6]),(0,[z0,z2,z3,z871,z5,z6])],[(0,[z38,z0,z2,z3,z312,z6]),(0,[z2,z3,z4,z24,z368,z6]),(0,[z0,z2,z51,z25,z8,z6]),(0,[z38,z0,z1186,z3,z4,z6])],[(0,[z0,z2,z99,z34,z5,z6]),(0,[z0,z2,z3,z4,z1269,z6])],[(0,[z191,z0,z3,z4,z24,z28]),(0,[z251,z2,z3,z4,z24,z6]),(0,[z0,z2,z1270,z4,z5,z6]),(0,[z38,z0,z2,z3,z4,z28]),(0,[z0,z222,z3,z173,z5,z82]),(0,[z38,z0,z2,z1271,z4,z6]),(0,[z0,z2,z1271,z4,z5,z6])],[(0,[z0,z2,z3,z4,z1272,z6]),(0,[z58,z0,z2,z99,z5,z6])],[(0,[z0,z2,z3,z4,z1273,z6]),(0,[z0,z2,z3,z4,z5,z1274]),(0,[z0,z2,z3,z4,z1275,z6]),(0,[z0,z2,z126,z4,z8,z6])],[(0,[z0,z2,z3,z4,z26,z179]),(0,[z0,z2,z3,z4,z1276,z6]),(0,[z0,z2,z509,z4,z5,z6]),(0,[z0,z2,z147,z4,z823,z6]),(0,[z0,z2,z3,z4,z271,z6])],[(0,[z797,z123,z3,z4,z5,z6]),(0,[z760,z0,z2,z3,z4,z6]),(0,[z0,z2,z764,z91,z5,z6]),(0,[z38,z0,z718,z3,z4,z6])]],
   [[(0,[z0,z2,z3,z172,z5,z6]),(0,[z0,z2,z3,z4,z1277,z6])],[(0,[z227,z0,z711,z3,z4,z6]),(0,[z0,z31,z3,z4,z24,z6])],[(0,[z0,z2,z1278,z4,z5,z6]),(0,[z227,z0,z2,z123,z3,z4]),(0,[z41,z227,z0,z2,z3,z4]),(0,[z0,z2,z3,z4,z213,z49]),(0,[z0,z2,z1021,z3,z26,z6])],[(0,[z191,z0,z3,z4,z26,z28])],[(0,[z0,z1279,z3,z4,z5,z6]),(0,[z0,z2,z263,z184,z5,z6])],[(0,[z0,z291,z3,z4,z5,z6]),(0,[z38,z0,z2,z99,z91,z6]),(0,[z0,z2,z3,z4,z1280,z6])],[(0,[z0,z2,z268,z4,z8,z6]),(0,[z0,z2,z223,z4,z198,z53])],[(0,[z0,z2,z3,z92,z232,z6]),(0,[z0,z2,z3,z4,z6,z1281])],[(0,[z0,z2,z4,z112,z8,z6])],[(0,[z0,z31,z3,z4,z26,z6]),(0,[z0,z2,z135,z4,z248,z6])],[(0,[z0,z27,z188,z4,z5,z6]),(0,[z38,z0,z31,z3,z4,z28]),(0,[z0,z2,z3,z4,z6,z1059]),(0,[z0,z2,z3,z4,z1282,z6])],[(0,[z29,z0,z3,z4,z163,z6]),(0,[z0,z2,z3,z4,z6,z1283]),(0,[z0,z2,z3,z5,z1284,z6])],[(0,[z0,z2,z3,z4,z5,z1285]),(0,[z0,z2,z3,z4,z208,z6]),(0,[z1286,z0,z2,z3,z4,z6]),(1,[z227,z0,z711,z3,z4]),(0,[z227,z0,z2,z3,z4,z202]),(0,[z0,z2,z3,z1287,z5,z6]),(0,[z0,z2,z4,z8,z6,z388])],[(0,[z7,z2,z105,z4,z24,z6]),(0,[z0,z2,z3,z4,z1288,z6]),(0,[z0,z2,z3,z4,z1289,z6])],[(0,[z0,z2,z3,z4,z1290,z6]),(1,[z0,z2,z764,z5,z6]),(0,[z0,z2,z469,z3,z4,z6]),(0,[z0,z3,z4,z5,z6,z1158])],[(0,[z1291,z0,z2,z3,z4,z6]),(0,[z38,z0,z2,z3,z419,z6]),(0,[z0,z2,z3,z817,z5,z6]),(0,[z0,z2,z257,z3,z8,z6]),(0,[z0,z2,z3,z8,z6,z935])]],
   [[(0,[z38,z0,z3,z562,z4,z6]),(0,[z0,z1292,z3,z4,z5,z6]),(0,[z227,z0,z2,z223,z3,z4]),(0,[z0,z2,z3,z4,z444,z6]),(0,[z0,z2,z3,z26,z6,z182])],[(0,[z1293,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z26,z310]),(0,[z0,z2,z3,z4,z753,z6])],[(0,[z227,z103,z0,z2,z3,z4])],[(0,[z0,z2,z268,z4,z68,z6]),(0,[z0,z2,z3,z4,z1294,z6]),(0,[z0,z3,z4,z5,z6,z1295]),(0,[z0,z2,z99,z764,z5,z6]),(0,[z0,z2,z51,z5,z6,z480])],[(0,[z0,z2,z3,z4,z6,z1296]),(0,[z1297,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z9,z6]),(0,[z0,z1298,z3,z4,z5,z6]),(0,[z37,z0,z43,z3,z4,z6])],[(0,[z0,z936,z3,z4,z5,z6]),(0,[z490,z0,z2,z422,z4,z6])],[(0,[z0,z2,z145,z312,z5,z6]),(0,[z2,z3,z4,z122,z26,z6]),(0,[z0,z2,z99,z623,z91,z6]),(0,[z0,z1063,z3,z4,z5,z6])],[(0,[z0,z2,z3,z1299,z5,z6]),(0,[z168,z2,z161,z4,z409,z6]),(0,[z0,z2,z3,z4,z1300,z6])],[(0,[z0,z2,z3,z312,z5,z6]),(0,[z0,z2,z4,z5,z53,z673])],[(0,[z84,z278,z3,z4,z5,z6]),(0,[z0,z2,z99,z631,z5,z6]),(0,[z39,z2,z3,z15,z5,z6]),(0,[z0,z254,z761,z4,z5,z6]),(0,[z0,z43,z3,z4,z5,z6]),(0,[z0,z2,z1301,z4,z5,z6])],[(0,[z0,z2,z3,z4,z24,z60]),(0,[z0,z3,z52,z331,z5,z6]),(0,[z0,z2,z3,z4,z1302,z6]),(0,[z227,z0,z2,z3,z4,z127]),(0,[z0,z1043,z3,z4,z26,z6]),(0,[z0,z2,z4,z26,z6,z388]),(0,[z0,z2,z3,z4,z315,z8]),(0,[z38,z0,z2,z3,z4,z435]),(0,[z29,z0,z31,z3,z4,z6]),(0,[z106,z0,z2,z5,z388,z127]),(0,[z0,z3,z4,z8,z6,z324])],[(0,[z0,z2,z145,z4,z8,z6]),(0,[z0,z2,z1303,z3,z4,z6]),(0,[z0,z2,z1264,z4,z5,z6])],[],[(0,[z0,z2,z3,z4,z24,z6]),(0,[z0,z2,z3,z4,z73,z60]),(0,[z38,z103,z62,z3,z4,z6]),(0,[z0,z2,z1304,z4,z5,z6]),(0,[z227,z0,z2,z3,z4,z28]),(0,[z0,z2,z135,z4,z8,z6])],[(0,[z0,z2,z3,z146,z24,z6]),(0,[z2,z765,z161,z4,z5,z6]),(0,[z0,z2,z3,z1305,z5,z6])],[(0,[z0,z2,z923,z3,z5,z6]),(0,[z0,z43,z3,z4,z57,z6])]],
   [[(0,[z0,z2,z3,z4,z73,z6]),(0,[z0,z2,z3,z4,z1306,z6]),(0,[z0,z2,z75,z4,z5,z6]),(0,[z0,z2,z3,z4,z1307,z6]),(0,[z48,z144,z2,z3,z4,z5]),(0,[z0,z2,z3,z1308,z4,z6])],[(0,[z0,z2,z3,z146,z73,z6])],[(0,[z0,z2,z3,z4,z26,z60]),(0,[z1240,z0,z2,z3,z4,z6]),(0,[z39,z2,z3,z15,z178,z6]),(0,[z0,z40,z362,z4,z5,z6])],[(0,[z38,z0,z2,z3,z4,z626])],[(0,[z0,z2,z188,z312,z5,z6]),(0,[z48,z37,z0,z2,z3,z4]),(0,[z0,z2,z1309,z3,z5,z6]),(0,[z38,z0,z2,z3,z4,z488])],[(0,[z0,z2,z3,z4,z26,z6])],[(0,[z0,z2,z3,z146,z26,z6]),(0,[z0,z2,z18,z4,z377,z6]),(0,[z687,z2,z3,z4,z26,z6]),(0,[z69,z0,z50,z2,z3,z4]),(0,[z0,z1310,z3,z4,z5,z6]),(0,[z38,z191,z0,z3,z4,z28])],[(0,[z103,z62,z3,z4,z24,z6]),(0,[z0,z2,z3,z4,z1311,z6])],[(0,[z0,z3,z4,z5,z6,z1312]),(0,[z0,z61,z3,z4,z5,z425]),(0,[z38,z0,z2,z876,z3,z6])],[(0,[z0,z2,z188,z4,z24,z6]),(0,[z0,z2,z3,z1313,z5,z6]),(0,[z0,z2,z3,z4,z1314,z6]),(0,[z0,z320,z3,z4,z57,z6])],[(0,[z0,z3,z4,z1315,z5,z6]),(0,[z0,z2,z3,z108,z5,z6]),(0,[z447,z2,z3,z4,z24,z6]),(0,[z0,z2,z135,z4,z68,z6])],[(0,[z1146,z0,z2,z3,z4,z6]),(0,[z94,z2,z3,z4,z179,z24])],[(0,[z0,z2,z188,z4,z73,z6]),(0,[z48,z38,z0,z43,z3,z4])],[(0,[z38,z0,z63,z3,z4,z28])],[(0,[z38,z0,z2,z3,z146,z6]),(0,[z0,z320,z3,z4,z452,z6]),(0,[z38,z0,z2,z3,z4,z655]),(0,[z0,z2,z3,z4,z1316,z6])],[(0,[z103,z62,z3,z4,z26,z6]),(0,[z227,z0,z2,z3,z4,z49])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 497) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 497).take 504) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1001).take 398) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1399)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [497, 504, 398] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 117).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 117).take 119).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 236).take 123).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 359).take 117).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 476).take 36).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [117, 119, 123, 117, 36] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_nil pcend)))))

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

end PEqualNP.Outside.L_meta_38689

theorem PEqualNP.Outside.L_meta_38689 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808392 * 2 ^ 32 + 4241017032) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808392 * 2 ^ 32 + 4241017032) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38689.solve