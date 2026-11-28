import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38253

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
  Nat.testBit (4008241864 * 2 ^ 32 + 3940597952) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x20023635c62dc798#64 ++ 0x10011b1ae316e3cc#64 ++ 0xbe867e7fce7fcf99#64 ++ 0x5f433f3fe73fe7cc#64 : BitVec 256),
   (0x00388a8c1a9c50aa#64 ++ 0x001c45460d4e2855#64 ++ 0xff798f8c7f9c71ff#64 ++ 0xffbcc7c63fce38ff#64 : BitVec 256),
   (0x0781517061602b54#64 ++ 0x03c0a8b830b015aa#64 ++ 0xef81f1f071e07fff#64 ++ 0xf7c0f8f838f03fff#64 : BitVec 256),
   (0x11dc01de81f681e0#64 ++ 0x88ee00ef40fb40f0#64 ++ 0x37fe01ff81ff81e1#64 ++ 0x9bff00ffc0ffc0f0#64 : BitVec 256),
   (0x8befee0001db7c00#64 ++ 0x45f7f70000edbe00#64 ++ 0x3bfffe0001fffe00#64 ++ 0x1dffff0000ffff00#64 : BitVec 256),
   (0x5df7fdeb7c000000#64 ++ 0x2efbfef5be000000#64 ++ 0x3dfffffffe000000#64 ++ 0x1effffffff000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [1, 3]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [6, 5]⟩, ⟨.and, [7, 4]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [2, 10]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [0, 13]⟩, ⟨.or, [14, 12]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00388a8c1a9c50aa 0x001c45460d4e2855 0xff798f8c7f9c71ff 0xffbcc7c63fce38ff

def z1 : W := mkw 0x0781517061602b54 0x03c0a8b830b015aa 0xef81f1f071e07fff 0xf7c0f8f838f03fff

def z2 : W := mkw 0x09c7640000000000 0x04e3b20000000000 0x0086700000000000 0x0043380000000000

def z3 : W := mkw 0x11dc01de81f681e0 0x88ee00ef40fb40f0 0x37fe01ff81ff81e1 0x9bff00ffc0ffc0f0

def z4 : W := mkw 0x20023635c62dc798 0x10011b1ae316e3cc 0xbe867e7fce7fcf99 0x5f433f3fe73fe7cc

def z5 : W := mkw 0x5df7fdeb7c000000 0x2efbfef5be000000 0x3dfffffffe000000 0x1effffffff000000

def z6 : W := mkw 0x8befee0001db7c00 0x45f7f70000edbe00 0x3bfffe0001fffe00 0x1dffff0000ffff00

def z7 : W := mkw 0x22000214836defdc 0x1100010a41b6f7ee 0xc200000001ffffff 0xe100000000ffffff

def z8 : W := mkw 0x2000000586048088 0x10000002c3024044 0x0000000f8e000000 0x00000007c7000000

def z9 : W := mkw 0x01fc8a8c1bde50aa 0x00fe45460def2855 0xffff8f8c7ffff1ff 0xffffc7c63ffff8ff

def z10 : W := mkw 0x0000000000000000 0x0000000000000000 0xef018180718071ff 0xf780c0c038c038ff

def z11 : W := mkw 0x0781517061602b54 0x03c0a8b830b015aa 0x0080707000600e00 0x0040383800300700

def z12 : W := mkw 0x11dc01de81f681e0 0x88ee00ef40fb40f0 0x10fe007f807f8000 0x087f003fc03fc000

def z13 : W := mkw 0x203abebddebdd7ba 0x101d5f5eef5eebdd 0xffffffffffffffff 0xffffffffffffffff

def z14 : W := mkw 0x0018009c80b481a0 0x000c004e405a40d0 0x37fe01ff81ff81e1 0x9bff00ffc0ffc0f0

def z15 : W := mkw 0x5ddf75ffe5f681e0 0xaeefbafff2fb40f0 0x37fe71ff81ff81e1 0x9bff38ffc0ffc0f0

def z16 : W := mkw 0xa208021483ffff98 0x5104010a41ffffcc 0x8200000001ffff99 0x4100000000ffffcc

def z17 : W := mkw 0x29e7fe35c62dc798 0x14f3ff1ae316e3cc 0xbffffe7fce7fcf99 0x5fffff3fe73fe7cc

def z18 : W := mkw 0x9bdf65de81f7ade0 0xcdefb2ef40fbd6f0 0x37fe71ff81ff8fe1 0x9bff38ffc0ffc7f0

def z19 : W := mkw 0x0000102040000000 0x0000081020000000 0x2c80707040000000 0x1640383820000000

def z20 : W := mkw 0x20000214822dc798 0x1000010a4116e3cc 0xb686007f807fcf99 0x5b43003fc03fe7cc

def z21 : W := mkw 0x00388a8818985022 0x001c45440c4c2811 0x7b798f80319c7066 0xbdbcc7c018ce3833

def z22 : W := mkw 0x8bffee8c1bdf7caa 0x45fff7460defbe55 0x3bfffe0c0ffffe00 0x1dffff0607ffff00

def z23 : W := mkw 0x01cc000001d20000 0x00e6000000e90000 0x33fe000001ff8000 0x19ff000000ffc000

def z24 : W := mkw 0x11fc8bde9bfed1ea 0x88fe45ef4dff68f5 0xffff8ffffffff1ff 0xffffc7fffffff8ff

def z25 : W := mkw 0x20023431c4218710 0x10011a18e210c388 0x0086707380638e00 0x00433839c031c700

def z26 : W := mkw 0x2002363146294718 0x10011b18a314a38c 0xae807e704e604f99 0x57403f38273027cc

def z27 : W := mkw 0x0381400001402800 0x01c0a00000a01400 0x2b81f00001e07e00 0x15c0f80000f03f00

def z28 : W := mkw 0x20000214822dc798 0x1000010a4116e3cc 0x82000000007fcf99 0x41000000003fe7cc

def z29 : W := mkw 0x5df5c9ca38000000 0x2efae4e51c000000 0x0179818030000000 0x00bcc0c018000000

def z30 : W := mkw 0x4c33fca97c000000 0x2619fe54be000000 0x3d79ff8c7e000000 0x1ebcffc63f000000

def z31 : W := mkw 0x00000204020c4088 0x0000010201062044 0xbe000e0c4e1c4199 0x5f000706270e20cc

def z32 : W := mkw 0x0018008c009400a0 0x000c0046004a0050 0xff79818c719c71ff 0xffbcc0c638ce38ff

def z33 : W := mkw 0x8ffffffc7bff7ffe 0x47fffffe3dffbfff 0xfffffffc7fffffff 0xfffffffe3fffffff

def z34 : W := mkw 0x0002342144000000 0x00011a10a2000000 0x0086707380000000 0x00433839c0000000

def z35 : W := mkw 0x101001de802481e0 0x880800ef401240f0 0x040001ff800001e1 0x820000ffc00000f0

def z36 : W := mkw 0x8bc7640001432c00 0x45e3b20000a19600 0x0086700000638e00 0x004338000031c700

def z37 : W := mkw 0x0601503061602b54 0x0300a81830b015aa 0xca01f00071e07fff 0xe500f80038f03fff

def z38 : W := mkw 0x11dc01ca01d20060 0x88ee00e500e90030 0x35fe01ff81800060 0x9aff00ffc0c00030

def z39 : W := mkw 0x2022be215e09561a 0x10115f10af04ab0d 0xc801fe007e007e1e 0x6400ff003f003f0f

def z40 : W := mkw 0x0002342144000000 0x00011a10a2000000 0x3c867e7fce000000 0x1e433f3fe7000000

def z41 : W := mkw 0x00080204029c50aa 0x00040102014e2855 0xc2000000019c71ff 0xe100000000ce38ff

def z42 : W := mkw 0x0581414020000000 0x02c0a0a010000000 0x0101818030000000 0x0080c0c018000000

def z43 : W := mkw 0x0002260000094400 0x000113000004a200 0x3a867e00007fce00 0x1d433f00003fe700

def z44 : W := mkw 0xabeffe35c7ffff98 0x55f7ff1ae3ffffcc 0xbffffe7fcfffff99 0x5fffff3fe7ffffcc

def z45 : W := mkw 0x82388a8c1bdf7caa 0x411c45460defbe55 0xff798f8c7fffffff 0xffbcc7c63fffffff

def z46 : W := mkw 0x119001de816481e0 0x88c800ef40b240f0 0x278001ff81e001e1 0x93c000ffc0f000f0

def z47 : W := mkw 0x041011fc7a2403fe 0x020808fe3d1201ff 0xc40001fc7e0001ff 0xe20000fe3f0000ff

def z48 : W := mkw 0x11dc01ce009400a0 0x08ee00e7004a0050 0x37fe01ff819c01e1 0x9bff00ffc0ce00f0

def z49 : W := mkw 0x5dc7756364000000 0x2ee3bab1b2000000 0x0086707380000000 0x00433839c0000000

def z50 : W := mkw 0x11d635eb44000000 0x08eb1af5a2000000 0x3dfe7fffce000000 0x1eff3fffe7000000

def z51 : W := mkw 0x31de37ffc7ffc7f8 0x98ef1bffe3ffe3fc 0xbffe7fffcfffcff9 0xdfff3fffe7ffe7fc

def z52 : W := mkw 0x09e7ee0000094400 0x04f3f7000004a200 0x3bfffe00007fce00 0x1dffff00003fe700

def z53 : W := mkw 0x0010008c1a0400aa 0x000800460d020055 0x0000000c0e000000 0x0000000607000000

def z54 : W := mkw 0x11de35ffc5f681e0 0x88ef1affe2fb40f0 0x3ffe7fffcfff81e1 0x9fff3fffe7ffc0f0

def z55 : W := mkw 0xdfffefca39db7c00 0x6ffff7e51cedbe00 0x3bffff8031fffe00 0x1dffffc018ffff00

def z56 : W := mkw 0x019801dc01f401e0 0x00cc00ee00fa00f0 0x37f801fc01fc01e1 0x9bfc00fe00fe00f0

def z57 : W := mkw 0x0030888818000000 0x001844440c000000 0x3d798f8c7e000000 0x1ebcc7c63f000000

def z58 : W := mkw 0x5dffffef7e9c50aa 0x2efffff7bf4e2855 0xffffffffff9c71ff 0xffffffffffce38ff

def z59 : W := mkw 0x20000214822dc798 0x1000010a4116e3cc 0xbe000e0c4e7fcf99 0x5f000706273fe7cc

def z60 : W := mkw 0x00288a0000985000 0x00144500004c2800 0x3b798e00019c7000 0x1dbcc70000ce3800

def z61 : W := mkw 0x8befee0001db7c00 0x45f7f70000edbe00 0x0979fe0001807e00 0x04bcff0000c03f00

def z62 : W := mkw 0x11d401ca00000000 0x08ea00e500000000 0x35fe01ff80000000 0x1aff00ffc0000000

def z63 : W := mkw 0x11dc01de81f681e0 0x88ee00ef40fb40f0 0x0378018001ff81e1 0x81bc00c000ffc0f0

def z64 : W := mkw 0x09e7ec0000000000 0x04f3f60000000000 0x39fffe0000000000 0x1cffff0000000000

def z65 : W := mkw 0x0000001081628140 0x8000000840b140a0 0x0000000000638000 0x000000000031c000

def z66 : W := mkw 0x0400117060200354 0x020008b8301001aa 0xc40001f0700001ff 0xe20000f8380000ff

def z67 : W := mkw 0x886eae00009b5400 0x44375700004daa00 0x107e0e00001f8000 0x083f0700000fc000

def z68 : W := mkw 0x0000001480248180 0x0000000a401240c0 0x3686007f807f8181 0x1b43003fc03fc0c0

def z69 : W := mkw 0x0000103040200310 0x0000081820100188 0xef81f1f071e07fff 0xf7c0f8f838f03fff

def z70 : W := mkw 0x8bc76600014b6c00 0x45e3b30000a5b600 0x3a867e00007fce00 0x1d433f00003fe700

def z71 : W := mkw 0x0781415021602944 0x03c0a0a810b014a2 0x678181f031e031e7 0xb3c0c0f818f018f3

def z72 : W := mkw 0x0000001000200100 0x0000000800100080 0x2680007000600181 0x13400038003000c0

def z73 : W := mkw 0x8a23ee0000097c00 0x4511f7000004be00 0x0801fe0000007e00 0x0400ff0000003f00

def z74 : W := mkw 0x20001035c6248398 0x1000081ae31241cc 0x8400007fce000199 0x4200003fe70000cc

def z75 : W := mkw 0x8bedc80001d23800 0x45f6e40000e91c00 0x0179800001803000 0x00bcc00000c01800

def z76 : W := mkw 0x0601400020002804 0x0300a00010001402 0x4001800030003006 0x2000c00018001803

def z77 : W := mkw 0x83cc020001db7c00 0x41e6010000edbe00 0x33fe000001fffe00 0x19ff000000ffff00

def z78 : W := mkw 0x0020880018000000 0x001044000c000000 0x08018e007e000000 0x0400c7003f000000

def z79 : W := mkw 0x000000001a00000a 0x000000000d000005 0xc00000007e00001e 0x600000003f00000f

def z80 : W := mkw 0x8bffee8c1bdf7caa 0x45fff7460defbe55 0xffffff8c7fffffff 0xffffffc63fffffff

def z81 : W := mkw 0x59f6adcb1c000000 0x2cfb56e58e000000 0x35fe0fff8e000000 0x1aff07ffc7000000

def z82 : W := mkw 0x8a03640000012c00 0x4501b20000009600 0x0000700000000e00 0x0000380000000700

def z83 : W := mkw 0x17c55172e162ab54 0x8be2a8b970b155aa 0xef87f1f3f1e3ffff 0xf7c3f8f9f8f1ffff

def z84 : W := mkw 0x5df7fdfb7d600140 0x2efbfefdbeb000a0 0x3fffffffffe001e1 0x9ffffffffff000f0

def z85 : W := mkw 0x8822ae0000095400 0x441157000004aa00 0x00000e0000000000 0x0000070000000000

def z86 : W := mkw 0x00388a8c1a9c50aa 0x001c45460d4e2855 0x51798f8c3f9c3066 0xa8bcc7c61fce1833

def z87 : W := mkw 0x203aae8d9e9dd4aa 0x101d5746cf4eea55 0xff7f8f8fff9ff1ff 0xffbfc7c7ffcff8ff

def z88 : W := mkw 0x07b9dbfc7bfc7bfe 0x03dcedfe3dfe3dff 0xfff9fffc7ffc7fff 0xfffcfffe3ffe3fff

def z89 : W := mkw 0x01ce260001db4400 0x00e7130000eda200 0x3bfe7e0001ffce00 0x1dff3f0000ffe700

def z90 : W := mkw 0x8befee1481fffde0 0xc5f7f70a40fffef0 0x3bfffe0001ffffe1 0x9dffff0000fffff0

def z91 : W := mkw 0x0018008c009400a0 0x000c0046004a0050 0x3778018c019c01e1 0x9bbc00c600ce00f0

def z92 : W := mkw 0x002aae0000995400 0x00155700004caa00 0x3bfffe0001fffe00 0x1dffff0000ffff00

def z93 : W := mkw 0x0008001481f681e0 0x8004000a40fb40f0 0x0200000001ff81e1 0x8100000000ffc0f0

def z94 : W := mkw 0x20023635c62dc798 0x10011b1ae316e3cc 0xff87ffffffffffff 0xffc3ffffffffffff

def z95 : W := mkw 0x0581517061600140 0x02c0a8b830b000a0 0x2f81f1f071e001e1 0x97c0f8f838f000f0

def z96 : W := mkw 0x0783757165602b54 0x03c1bab8b2b015aa 0xff87ffffffe07fff 0xffc3fffffff03fff

def z97 : W := mkw 0x17dd51fee1f6abf4 0x8beea8ff70fb55fa 0xfffff1fff1ffffff 0xfffff8fff8ffffff

def z98 : W := mkw 0x00208a001a08500a 0x001045000d042805 0xc8018e007e00701e 0x6400c7003f00380f

def z99 : W := mkw 0x887eae8c1a9f54aa 0x443f57460d4faa55 0x107e0e0c0e1f8000 0x083f0706070fc000

def z100 : W := mkw 0x03b9ca8c1bdc78aa 0x01dce5460dee3c55 0xfff9ff8c7ffc7fff 0xfffcffc63ffe3fff

def z101 : W := mkw 0x541011fffc2481e0 0xaa0808fffe1240f0 0x040001fffe0001e1 0x820000ffff0000f0

def z102 : W := mkw 0x00000204020c4088 0x0000010201062044 0x82000000001c4199 0x41000000000e20cc

def z103 : W := mkw 0x0401502060000000 0x0200a81030000000 0x0801f00070000000 0x0400f80038000000

def z104 : W := mkw 0x8fefef4021db7c44 0x47f7f7a010edbe22 0x7bffff8031fffe66 0xbdffffc018ffff33

def z105 : W := mkw 0x01cc001481f68180 0x00e6000a40fb40c0 0x37fe007f81ff8181 0x1bff003fc0ffc0c0

def z106 : W := mkw 0x0010028c1a0c40aa 0x000801460d062055 0xfe000f8c7e1c41ff 0xff0007c63f0e20ff

def z107 : W := mkw 0x0030888818000000 0x001844440c000000 0x0179818030000000 0x00bcc0c018000000

def z108 : W := mkw 0x202abe35c6bdd798 0x10155f1ae35eebcc 0xbffffe7fcfffff99 0x5fffff3fe7ffffcc

def z109 : W := mkw 0x5ff5c9ca39402844 0x2ffae4e51ca01422 0x4179818031803066 0xa0bcc0c018c01833

def z110 : W := mkw 0x5c76bdeb7c000000 0x2e3b5ef5be000000 0x147e0ffffe000000 0x0a3f07ffff000000

def z111 : W := mkw 0x00208a041a0c508a 0x001045020d062845 0xfe018e0c7e1c719f 0x7f00c7063f0e38cf

def z112 : W := mkw 0x5df7fdeb7c000000 0x2efbfef5be000000 0x01fff1f3b0000000 0x00fff8f9d8000000

def z113 : W := mkw 0x9bffee8e81dffca0 0xcdfff74740effe50 0x3bfffe0f81fffe00 0x1dffff07c0ffff00

def z114 : W := mkw 0x00388a8c1a9c50aa 0x001c45460d4e2855 0xd4780f8c7e1c01ff 0xea3c07c63f0e00ff

def z115 : W := mkw 0x5df7fdeb7c000000 0x2efbfef5be000000 0xffffffffff8071ff 0xffffffffffc038ff

def z116 : W := mkw 0x8befee0001db7c00 0x45f7f70000edbe00 0x10fe7e00007f8e00 0x087f3f00003fc700

def z117 : W := mkw 0x5846240304000000 0x2c23120182000000 0x0006000380000000 0x00030001c0000000

def z118 : W := mkw 0x0030888818000000 0x001844440c000000 0x10780e0c0e000000 0x083c070607000000

def z119 : W := mkw 0x00388a8c1a9c50aa 0x001c45460d4e2855 0x10780e0c0e1c0000 0x083c0706070e0000

def z120 : W := mkw 0x0000001080208100 0x0000000840104080 0x0086007380638000 0x00430039c031c000

def z121 : W := mkw 0x5dfdc9ca38901022 0x2efee4e51c480811 0x4179818031803066 0xa0bcc0c018c01833

def z122 : W := mkw 0x00389abc5abc53ba 0x001c4d5e2d5e29dd 0xfff9fffc7ffc7fff 0xfffcfffe3ffe3fff

def z123 : W := mkw 0x5df7fdeb7c000000 0x2efbfef5be000000 0x10fe7e7f8e000000 0x087f3f3fc7000000

def z124 : W := mkw 0x0781414021402844 0x03c0a0a010a01422 0x4101818031803066 0xa080c0c018c01833

def z125 : W := mkw 0x09e7fc2144000000 0x04f3fe10a2000000 0x3dfffe7fce000000 0x1effff3fe7000000

def z126 : W := mkw 0x20022605860dc488 0x10011302c306e244 0xbe060e0fce1fc199 0x5f030707e70fe0cc

def z127 : W := mkw 0x886eae00009b5400 0x44375700004daa00 0x3b7f8e00019ff000 0x1dbfc70000cff800

def z128 : W := mkw 0x9ffffffee1fffff4 0xcfffffff70fffffa 0xfffffffff1ffffff 0xfffffffff8ffffff

def z129 : W := mkw 0x5dfdcbce3a9c50aa 0x2efee5e71d4e2855 0xff798f8c7f9c71ff 0xffbcc7c63fce38ff

def z130 : W := mkw 0x27837571e561af54 0x13c1bab8f2b0d7aa 0x0086707380638e00 0x00433839c031c700

def z131 : W := mkw 0x13dd41de81f6a9e0 0x89eea0ef40fb54f0 0x3ffff1ff81ffffe1 0x9ffff8ffc0fffff0

def z132 : W := mkw 0x8fc7757061632f54 0x47e3bab830b197aa 0x0086707000638e00 0x004338380031c700

def z133 : W := mkw 0xdffffdeb7dd23800 0x6ffffef5bee91c00 0x3dffffffff803000 0x1effffffffc01800

def z134 : W := mkw 0x8fefff7061fb7f54 0x47f7ffb830fdbfaa 0xfffffff071ffffff 0xfffffff838ffffff

def z135 : W := mkw 0x11dc01ca01d20000 0x08ee00e500e90000 0x37fe01ff81ff8000 0x1bff00ffc0ffc000

def z136 : W := mkw 0xdfffffeb7ddb7c00 0x6ffffff5beedbe00 0x3ffffffffffffe00 0x1fffffffffffff00

def z137 : W := mkw 0x0000000000000000 0x0000000000000000 0x4101818031803066 0xa080c0c018c01833

def z138 : W := mkw 0x11f489ca18000000 0x08fa44e50c000000 0x3dff8ffffe000000 0x1effc7ffff000000

def z139 : W := mkw 0x5876ac8b1c000000 0x2c3b56458e000000 0x107e0e0f8e000000 0x083f0707c7000000

def z140 : W := mkw 0x8fa3ff7061697f54 0x47d1ffb830b4bfaa 0xef81fff071e07fff 0xf7c0fff838f03fff

def z141 : W := mkw 0x0010008c000400a0 0x0008004600020050 0x0400018c000001e1 0x820000c6000000f0

def z142 : W := mkw 0x07b9d9f879f03b76 0x03dcecfc3cf81dbb 0xeff9f1f071e07fff 0xf7fcf8f838f03fff

def z143 : W := mkw 0x6c23fe217e094618 0x3611ff10bf04a30c 0x8801fe007e004e18 0x4400ff003f00270c

def z144 : W := mkw 0x7df7fffffe2dc798 0x3efbffffff16e3cc 0xbffffffffe7fcf99 0x5fffffffff3fe7cc

def z145 : W := mkw 0x541011eb7c000000 0x2a0808f5be000000 0x040001fffe000000 0x020000ffff000000

def z146 : W := mkw 0x31de35ffc5f787f0 0x98ef1affe2fbc3f8 0x37fe71ff81ff8fe1 0x9bff38ffc0ffc7f0

def z147 : W := mkw 0x8bffee8819db7c00 0x45fff7440cedbe00 0x3fffff8c7ffffe00 0x1fffffc63fffff00

def z148 : W := mkw 0x20388a9c9abdd7ba 0x101c454e4d5eebdd 0xff798f8c7fffffff 0xffbcc7c63fffffff

def z149 : W := mkw 0x8be7ec0001432c00 0x45f3f60000a19600 0x39fffe0000638e00 0x1cffff000031c700

def z150 : W := mkw 0x559151eb7c000000 0x2ac8a8f5be000000 0x2d81f1fffe000000 0x16c0f8ffff000000

def z151 : W := mkw 0x741011fffe248398 0x3a0808ffff1241cc 0x840001fffe000199 0x420000ffff0000cc

def z152 : W := mkw 0x8208020001db7c00 0x4104010000edbe00 0x0200000001fffe00 0x0100000000ffff00

def z153 : W := mkw 0x20023635c62dc798 0x10011b1ae316e3cc 0x10867e7f8e7f8e00 0x08433f3fc73fc700

def z154 : W := mkw 0x00000004020400aa 0x0000000201020055 0xc0000000000001ff 0xe0000000000000ff

def z155 : W := mkw 0x7df7fdfffe248398 0x3efbfeffff1241cc 0xbdfffffffe000199 0x5effffffff0000cc

def z156 : W := mkw 0x8befee001bdb7c0a 0x45f7f7000dedbe05 0xfbfffe007ffffe1e 0x7dffff003fffff0f

def z157 : W := mkw 0x8befee1481fffd80 0x45f7f70a40fffec0 0x3ffffe7f81ffff81 0x1fffff3fc0ffffc0

def z158 : W := mkw 0x0002260000094400 0x000113000004a200 0x08007e0000004e00 0x04003f0000002700

def z159 : W := mkw 0x07895174e1f6abf4 0x83c4a8ba70fb55fa 0xef81f1f071ffffff 0xf7c0f8f838ffffff

def z160 : W := mkw 0x543099eb7c000000 0x2a184cf5be000000 0x3d798ffffe000000 0x1ebcc7ffff000000

def z161 : W := mkw 0x0400014020000044 0x020000a010000022 0x4000018030000066 0xa00000c018000033

def z162 : W := mkw 0x0000000000000000 0x0000000000000000 0xc4000180700001ff 0xe20000c0380000ff

def z163 : W := mkw 0x8feffe2061db7e14 0x47f7ff1030edbf0a 0xfbfffe0071fffe1e 0x7dffff0038ffff0f

def z164 : W := mkw 0x00080004809680a0 0x80040002404b4050 0x00000000001f8000 0x00000000000fc000

def z165 : W := mkw 0x11dc01ca01d20060 0x88ee00e500e90030 0x0178018001800060 0x80bc00c000c00030

def z166 : W := mkw 0x0180015001600140 0x00c000a800b000a0 0x0080007000600000 0x0040003800300000

def z167 : W := mkw 0x0008021483fed1ea 0x8004010a41ff68f5 0xc200000001fff1ff 0xe100000000fff8ff

def z168 : W := mkw 0x09efee0000985000 0x04f7f700004c2800 0x3bfffe00019c7000 0x1dffff0000ce3800

def z169 : W := mkw 0x5ff7fdfb7d602b54 0x2ffbfefdbeb015aa 0xffffffffffe07fff 0xfffffffffff03fff

def z170 : W := mkw 0x11c4015281628140 0x88e200a940b140a0 0x0086007380638000 0x00430039c031c000

def z171 : W := mkw 0x0781517061602b54 0x03c0a8b830b015aa 0xae80707040604f99 0x57403838203027cc

def z172 : W := mkw 0x00022604020d4488 0x000113020106a244 0xbe867e0c4e7fcf99 0x5f433f06273fe7cc

def z173 : W := mkw 0x37df77ffe7ffeffc 0x9befbbfff3fff7fe 0xffffffffffffffff 0xffffffffffffffff

def z174 : W := mkw 0x04389bfc7abc53fe 0x021c4dfe3d5e29ff 0xff798ffc7f9c71ff 0xffbcc7fe3fce38ff

def z175 : W := mkw 0x00288a041a9c50aa 0x001445020d4e2855 0xca018e007f9c71ff 0xe500c7003fce38ff

def z176 : W := mkw 0x5df5d9eb7c000000 0x2efaecf5be000000 0x057981fffe000000 0x02bcc0ffff000000

def z177 : W := mkw 0x23837635c76def98 0x11c1bb1ae3b6f7cc 0xbf87fe7fcfffff99 0x5fc3ff3fe7ffffcc

def z178 : W := mkw 0x55dc11fffdf681e0 0xaaee08fffefb40f0 0x37fe01ffffff81e1 0x9bff00ffffffc0f0

def z179 : W := mkw 0x54389bef7e9c50aa 0x2a1c4df7bf4e2855 0xff798fffff9c71ff 0xffbcc7ffffce38ff

def z180 : W := mkw 0x00000214822cc188 0x0000010a411660c4 0xbe860e7fce7fc199 0x5f43073fe73fe0cc

def z181 : W := mkw 0x20001031c4208310 0x10000818e2104188 0x0000007380000000 0x00000039c0000000

def z182 : W := mkw 0x2008021483ffc7f8 0x9004010a41ffe3fc 0x8200000001ffcff9 0xc100000000ffe7fc

def z183 : W := mkw 0x00000014802481e0 0x8000000a401240f0 0x00000000000001e1 0x80000000000000f0

def z184 : W := mkw 0x5dfffdfffdf681e0 0xaefffefffefb40f0 0x3fffffffffff81e1 0x9fffffffffffc0f0

def z185 : W := mkw 0x27837775e76defdc 0x13c1bbbaf3b6f7ee 0xbe867e7fce7fcf99 0x5f433f3fe73fe7cc

def z186 : W := mkw 0x1054008a00000000 0x082a004500000000 0x107e000f80000000 0x083f0007c0000000

def z187 : W := mkw 0x0000000000000000 0x0000000000000000 0x2a80700000604e00 0x1540380000302700

def z188 : W := mkw 0x31de27df87ffc5e8 0x98ef13efc3ffe2f4 0x37fe0fff8fff81e1 0x9bff07ffc7ffc0f0

def z189 : W := mkw 0x20022605860dc488 0x10011302c306e244 0x10060e0f8e1f8000 0x08030707c70fc000

def z190 : W := mkw 0x01b88bdc1bfc51ea 0x00dc45ee0dfe28f5 0xfff98ffc7ffc71ff 0xfffcc7fe3ffe38ff

def z191 : W := mkw 0x00208a001a08500a 0x001045000d042805 0xef018f807f8071ff 0xf780c7c03fc038ff

def z192 : W := mkw 0x20001035c6248398 0x1000081ae31241cc 0xb686007fce7f8199 0x5b43003fe73fc0cc

def z193 : W := mkw 0x07a9db7061f87b54 0x03d4edb830fc3daa 0xfff9fff071fc7fff 0xfffcfff838fe3fff

def z194 : W := mkw 0x11dc01de9bf681ea 0x88ee00ef4dfb40f5 0xf7fe01ffffff81ff 0xfbff00ffffffc0ff

def z195 : W := mkw 0x00388a8c1a9c50aa 0x001c45460d4e2855 0x3d798f8c7e1c0000 0x1ebcc7c63f0e0000

def z196 : W := mkw 0x00388a8c1a9c50aa 0x001c45460d4e2855 0xc3798180319c71ff 0xe1bcc0c018ce38ff

def z197 : W := mkw 0x27815374e36defdc 0x13c0a9ba71b6f7ee 0xef81f1f071ffffff 0xf7c0f8f838ffffff

def z198 : W := mkw 0x5dffffef7e9c50aa 0x2efffff7bf4e2855 0x3dfffffffe1c0000 0x1effffffff0e0000

def z199 : W := mkw 0x05b9dbec7a9c50aa 0x02dcedf63d4e2855 0xfff9fffc7f9c71ff 0xfffcfffe3fce38ff

def z200 : W := mkw 0xdbffee8b1ddb7c00 0x6dfff7458eedbe00 0x3bfffe0f8ffffe00 0x1dffff07c7ffff00

def z201 : W := mkw 0x00001034c0248390 0x0000081a601241c8 0xbe86707fc07fcf99 0x5f43383fe03fe7cc

def z202 : W := mkw 0x0000103040200310 0x0000081820100188 0xae80707040604f99 0x57403838203027cc

def z203 : W := mkw 0x0383660001496c00 0x01c1b30000a4b600 0x3b87fe0001fffe00 0x1dc3ff0000ffff00

def z204 : W := mkw 0x00388a8c1a9c50aa 0x001c45460d4e2855 0xd2780e0c0f9c71ff 0xe93c070607ce38ff

def z205 : W := mkw 0x00388a9c9bfed1ea 0x801c454e4dff68f5 0xff798f8c7ffff1ff 0xffbcc7c63ffff8ff

def z206 : W := mkw 0x09e5c80000000000 0x04f2e40000000000 0x0179800000000000 0x00bcc00000000000

def z207 : W := mkw 0x20023631c629c718 0x10011b18e314e38c 0x88867e73ce63ce18 0x44433f39e731e70c

def z208 : W := mkw 0x200a3635c6bdd7ba 0x10051b1ae35eebdd 0xfe867e7fcfffffff 0xff433f3fe7ffffff

def z209 : W := mkw 0xdff7fdeb7d432c00 0x6ffbfef5bea19600 0x3dfffffffe638e00 0x1effffffff31c700

def z210 : W := mkw 0x8fedc94021d23844 0x47f6e4a010e91c22 0x4179818031803066 0xa0bcc0c018c01833

def z211 : W := mkw 0x4c23fc217c000000 0x2611fe10be000000 0x0801fe007e000000 0x0400ff003f000000

def z212 : W := mkw 0x0018009c81f681e0 0x800c004e40fb40f0 0x3778018c01ff81e1 0x9bbc00c600ffc0f0

def z213 : W := mkw 0x11dc11fec1f683f0 0x88ee08ff60fb41f8 0xbffe71ffc1ffcff9 0xdfff38ffe0ffe7fc

def z214 : W := mkw 0x301011ffc62483f8 0x980808ffe31241fc 0x840001ffce0001f9 0xc20000ffe70000fc

def z215 : W := mkw 0x7dfffffffebdd7ba 0x3effffffff5eebdd 0xffffffffffffffff 0xffffffffffffffff

def z216 : W := mkw 0x5dfffdeffc9680a0 0xaefffef7fe4b4050 0x3dfffffffe1f8000 0x1effffffff0fc000

def z217 : W := mkw 0x5ff7fdeb7d402844 0x2ffbfef5bea01422 0x7dffffffff803066 0xbeffffffffc01833

def z218 : W := mkw 0x09efec0001d20000 0x04f7f60000e90000 0x3bfffe0001ff8000 0x1dffff0000ffc000

def z219 : W := mkw 0x587eae8f1e9c50aa 0x2c3f57478f4e2855 0xff7f8f8fff9c71ff 0xffbfc7c7ffce38ff

def z220 : W := mkw 0x8bfdc88819d23822 0x45fee4440ce91c11 0x4179818031803066 0xa0bcc0c018c01833

def z221 : W := mkw 0x5fffffff7ffc7bfe 0x2fffffffbffe3dff 0xfffffffffffc7fff 0xfffffffffffe3fff

def z222 : W := mkw 0x17dd51fee1f6abf4 0x8beea8ff70fb55fa 0x37fe71ff81ff8fe1 0x9bff38ffc0ffc7f0

def z223 : W := mkw 0x0381400001402800 0x01c0a00000a01400 0xef81f18071e07fff 0xf7c0f8c038f03fff

def z224 : W := mkw 0x24001175e62483dc 0x120008baf31241ee 0xc40001fffe0001ff 0xe20000ffff0000ff

def z225 : W := mkw 0x0581516060000000 0x02c0a8b030000000 0x2d81f1f070000000 0x16c0f8f838000000

def z226 : W := mkw 0x0038888c189400a0 0x001c44460c4a0050 0x3f798f8c7f9c01e1 0x9fbcc7c63fce00f0

def z227 : W := mkw 0x101801de81f681e0 0x880c00ef40fb40f0 0x060001ff81ff81e1 0x830000ffc0ffc0f0

def z228 : W := mkw 0x27bbfffdfffdfffe 0x13ddfffefffeffff 0xffffffffffffffff 0xffffffffffffffff

def z229 : W := mkw 0x0008020000985000 0x00040100004c2800 0x02000000019c7000 0x0100000000ce3800

def z230 : W := mkw 0x17c55172e162ab54 0x8be2a8b970b155aa 0x0086707380638e00 0x00433839c031c700

def z231 : W := mkw 0x11dc01ce81d680e0 0x88ee00e740eb4070 0x117e018f819f8060 0x88bf00c7c0cfc030

def z232 : W := mkw 0x11dc01de81f681e0 0x88ee00ef40fb40f0 0x057801ff818001e1 0x82bc00ffc0c000f0

def z233 : W := mkw 0x0000103040200310 0x0000081820100188 0x0080707000600e00 0x0040383800300700

def z234 : W := mkw 0x4c21c80038000000 0x2610e4001c000000 0x0001800030000000 0x0000c00018000000

def z235 : W := mkw 0x2783777167696f5c 0x13c1bbb8b3b4b7ae 0xef81fff07fe07fff 0xf7c0fff83ff03fff

def z236 : W := mkw 0xabeffe31c5fbff10 0x55f7ff18e2fdff88 0x3bfffe7381fffe00 0x1dffff39c0ffff00

def z237 : W := mkw 0x5ffffdfffdf6abf4 0xaffffefffefb55fa 0xffffffffffffffff 0xffffffffffffffff

def z238 : W := mkw 0x0000000000000000 0x0000000000000000 0x2d01818070000000 0x1680c0c038000000

def z239 : W := mkw 0x7df7ffeb7e094618 0x3efbfff5bf04a30c 0xbdfffffffe004e18 0x5effffffff00270c

def z240 : W := mkw 0xffffffffffffff98 0x7fffffffffffffcc 0xbfffffffffffff99 0x5fffffffffffffcc

def z241 : W := mkw 0x5ff7fdeb7d402800 0x2ffbfef5bea01400 0x3fffffffffe07e00 0x1ffffffffff03f00

def z242 : W := mkw 0x0000000000000000 0x0000000000000000 0xc2000000018071ff 0xe100000000c038ff

def z243 : W := mkw 0x105c008e809680a0 0x882e0047404b4050 0x107e000f801f8000 0x083f0007c00fc000

def z244 : W := mkw 0x9bffefde81fffde0 0xcdfff7ef40fffef0 0x3fffffff81ffffe1 0x9fffffffc0fffff0

def z245 : W := mkw 0xaa23fe2146097e18 0x5511ff10a304bf0c 0x8801fe004e007e18 0x4400ff0027003f0c

def z246 : W := mkw 0x0180015001600140 0x00c000a800b000a0 0x278001f001e001e1 0x93c000f800f000f0

def z247 : W := mkw 0x09ffee8c1a9c50aa 0x04fff7460d4e2855 0xffffff8c7f9c71ff 0xffffffc63fce38ff

def z248 : W := mkw 0x1044000280028000 0x8822000140014000 0x0006000380038000 0x00030001c001c000

def z249 : W := mkw 0x0000001480248180 0x0000000a401240c0 0x02000000007f8181 0x01000000003fc0c0

def z250 : W := mkw 0x2002342144010610 0x10011a10a2008308 0x0000700000000e00 0x0000380000000700

def z251 : W := mkw 0x8200000001432c00 0x4100000000a19600 0x0000000000638e00 0x000000000031c700

def z252 : W := mkw 0x03cd400001d22800 0x01e6a00000e91400 0x3bfff00001fffe00 0x1dfff80000ffff00

def z253 : W := mkw 0x8bedca0001db7c00 0x45f6e50000edbe00 0x0379800001fffe00 0x01bcc00000ffff00

def z254 : W := mkw 0x201010bdde2483ba 0x1008085eef1241dd 0xc40001fffe0001ff 0xe20000ffff0000ff

def z255 : W := mkw 0x0002240104000000 0x0001120082000000 0x10060e0f8e000000 0x08030707c7000000

def z256 : W := mkw 0x8bedc80001d23800 0x45f6e40000e91c00 0x2bf9f00001e07e00 0x15fcf80000f03f00

def z257 : W := mkw 0x0002260000094400 0x000113000004a200 0x10060e00001f8000 0x08030700000fc000

def z258 : W := mkw 0xce23fe217c097c00 0x6711ff10be04be00 0x0801fe007e007e00 0x0400ff003f003f00

def z259 : W := mkw 0x5de7fd637c000000 0x2ef3feb1be000000 0x0887fe73fe000000 0x0443ff39ff000000

def z260 : W := mkw 0x0008000000901022 0x0004000000480811 0x4000000001803066 0xa000000000c01833

def z261 : W := mkw 0x01c4000000000000 0x00e2000000000000 0x31fe000000000000 0x18ff000000000000

def z262 : W := mkw 0x8beffe2145db7c00 0x45f7ff10a2edbe00 0x3ffffe7fcffffe00 0x1fffff3fe7ffff00

def z263 : W := mkw 0x05b1d9e878000000 0x02d8ecf43c000000 0x3df9fffc7e000000 0x1efcfffe3f000000

def z264 : W := mkw 0x105c008e809680a0 0x882e0047404b4050 0x377e018f819f81e1 0x9bbf00c7c0cfc0f0

def z265 : W := mkw 0x0010008800000000 0x0008004400000000 0x3578018c00000000 0x1abc00c600000000

def z266 : W := mkw 0x11c4014200000000 0x08e200a100000000 0x0086007380000000 0x00430039c0000000

def z267 : W := mkw 0x20023435c6258798 0x10011a1ae312c3cc 0x8486707fce638f99 0x4243383fe731c7cc

def z268 : W := mkw 0x21823775c76dc7d8 0x10c11bbae3b6e3ec 0xbf867fffcfffcff9 0xdfc33fffe7ffe7fc

def z269 : W := mkw 0x13dc01de81f6abf4 0x89ee00ef40fb55fa 0xf7fe01ff81ffffff 0xfbff00ffc0ffffff

def z270 : W := mkw 0x11fc8bde9bfed1ea 0x88fe45ef4dff68f5 0x37fe0fff8fff81e1 0x9bff07ffc7ffc0f0

def z271 : W := mkw 0x2002362146094618 0x10011b10a304a30c 0x88007e004e004e18 0x44003f002700270c

def z272 : W := mkw 0x11dc03de83fec1e8 0x88ee01ef41ff60f4 0xbffe0fffcfffc1f9 0xdfff07ffe7ffe0fc

def z273 : W := mkw 0x07b1d9f879602b54 0x03d8ecfc3cb015aa 0xfff9fffc7fe07fff 0xfffcfffe3ff03fff

def z274 : W := mkw 0x0020880000000000 0x0010440000000000 0x39798e0000000000 0x1cbcc70000000000

def z275 : W := mkw 0xafefff75e7ffffdc 0x57f7ffbaf3ffffee 0xffffffffffffffff 0xffffffffffffffff

def z276 : W := mkw 0x5dfffdef7c9400a0 0x2efffef7be4a0050 0x3fffffffff9c01e1 0x9fffffffffce00f0

def z277 : W := mkw 0x0200001001602b54 0x0100000800b015aa 0xef01818071e07fff 0xf780c0c038f03fff

def z278 : W := mkw 0x079151fc7b642bfe 0x03c8a8fe3db215ff 0xef81f1fc7fe07fff 0xf7c0f8fe3ff03fff

def z279 : W := mkw 0x101801de80b481e0 0x880c00ef405a40f0 0x377801ff819c01e1 0x9bbc00ffc0ce00f0

def z280 : W := mkw 0x8befee0001db7c00 0x45f7f70000edbe00 0x117f8e00019fb000 0x08bfc70000cfd800

def z281 : W := mkw 0x27837775e76defdc 0x13c1bbbaf3b6f7ee 0xff87ffffffffffff 0xffc3ffffffffffff

def z282 : W := mkw 0x0000001000200354 0x00000008001001aa 0xc0000000000001ff 0xe0000000000000ff

def z283 : W := mkw 0x0601502060002a14 0x0300a8103000150a 0xc801f00070007e1e 0x6400f80038003f0f

def z284 : W := mkw 0x00388a8c1a9c50aa 0x001c45460d4e2855 0x3b798e0c0f9c7000 0x1dbcc70607ce3800

def z285 : W := mkw 0x15dc11fee1f683f4 0x8aee08ff70fb41fa 0xf7fe01fff1ff81ff 0xfbff00fff8ffc0ff

def z286 : W := mkw 0x55d411eb7c000000 0x2aea08f5be000000 0x35fe01fffe000000 0x1aff00ffff000000

def z287 : W := mkw 0x8befec0001d23800 0x45f7f60000e91c00 0x39fffe0001803000 0x1cffff0000c01800

def z288 : W := mkw 0x0601502060002a14 0x0300a8103000150a 0xef01f18071807fff 0xf780f8c038c03fff

def z289 : W := mkw 0x5df7fdef7e0400aa 0x2efbfef7bf020055 0xfdfffffffe0001ff 0xfeffffffff0000ff

def z290 : W := mkw 0xddffffeb7c9b5400 0x6efffff5be4daa00 0x3dfffffffe1f8000 0x1effffffff0fc000

def z291 : W := mkw 0xabfffebddfffffba 0x55ffff5eefffffdd 0xffffffffffffffff 0xffffffffffffffff

def z292 : W := mkw 0x5dc7756364000000 0x2ee3bab1b2000000 0x3c867e7fce000000 0x1e433f3fe7000000

def z293 : W := mkw 0x8be7ee0000097c00 0x45f3f7000004be00 0x39fffe0000007e00 0x1cffff0000003f00

def z294 : W := mkw 0x0381503041602b10 0x01c0a81820b01588 0xaf81f07041e07f99 0x57c0f83820f03fcc

def z295 : W := mkw 0x0010008818000000 0x000800440c000000 0x0400018c7e000000 0x020000c63f000000

def z296 : W := mkw 0x5400116364000000 0x2a0008b1b2000000 0x0000007380000000 0x00000039c0000000

def z297 : W := mkw 0x0000000000000000 0x0000000000000000 0x32860000007f8000 0x19430000003fc000

def z298 : W := mkw 0x11d401da81628140 0x88ea00ed40b140a0 0x35fe01ff80638000 0x1aff00ffc031c000

def z299 : W := mkw 0x00288a001a98500a 0x001445000d4c2805 0xfb798e007f9c701e 0x7dbcc7003fce380f

def z300 : W := mkw 0x1010008e800480a0 0x8808004740024050 0x0000000f80000000 0x00000007c0000000

def z301 : W := mkw 0x00388a8c1a9c50aa 0x001c45460d4e2855 0xbe780e0c4e1c4199 0x5f3c0706270e20cc

def z302 : W := mkw 0x0000001480248180 0x0000000a401240c0 0x0400007f80000181 0x0200003fc00000c0

def z303 : W := mkw 0x8208020403df7caa 0x4104010201efbe55 0xc200000001ffffff 0xe100000000ffffff

def z304 : W := mkw 0x8a23ee0000097c00 0x4511f7000004be00 0x3a87fe00007ffe00 0x1d43ff00003fff00

def z305 : W := mkw 0x8e23fe2060097e14 0x4711ff103004bf0a 0xc801fe0070007e1e 0x6400ff0038003f0f

def z306 : W := mkw 0x587eac8f9c9680a0 0xac3f5647ce4b4050 0x107e0e0f8e1f8000 0x083f0707c70fc000

def z307 : W := mkw 0x07b9c9c839d03866 0x03dce4e41ce81c33 0x4179818031803066 0xa0bcc0c018c01833

def z308 : W := mkw 0x0010008c1a0400aa 0x000800460d020055 0xc400018c7e0001ff 0xe20000c63f0000ff

def z309 : W := mkw 0x2002260106094408 0x100113008304a204 0x00000e000e000000 0x0000070007000000

def z310 : W := mkw 0x0781516060002a14 0x03c0a8b03000150a 0xed81f1f070007e1e 0x76c0f8f838003f0f

def z311 : W := mkw 0x11d401de80248180 0x08ea00ef401240c0 0x37fe01ff807f8181 0x1bff00ffc03fc0c0

def z312 : W := mkw 0x22023635c76defdc 0x11011b1ae3b6f7ee 0xfe867e7fcfffffff 0xff433f3fe7ffffff

def z313 : W := mkw 0x00080204029c50aa 0x00040102014e2855 0xef018180719c71ff 0xf780c0c038ce38ff

def z314 : W := mkw 0x0018008800900020 0x000c004400480010 0x0178018001800060 0x80bc00c000c00030

def z315 : W := mkw 0x0be7ec0001402800 0x05f3f60000a01400 0x3bfffe0001e07e00 0x1dffff0000f03f00

def z316 : W := mkw 0x5dfdc9deb9f681e0 0xaefee4ef5cfb40f0 0x37ff81ffb1ff81e1 0x9bffc0ffd8ffc0f0

def z317 : W := mkw 0x9bfdc9de81f6b9e0 0xcdfee4ef40fb5cf0 0x37ff81ff81ffb1e1 0x9bffc0ffc0ffd8f0

def z318 : W := mkw 0x2000001080218710 0x100000084010c388 0x0000000000638e00 0x000000000031c700

def z319 : W := mkw 0x00023625460c4088 0x00011b12a3062044 0xbe867e7fce1c4199 0x5f433f3fe70e20cc

def z320 : W := mkw 0x99feafde81ffd5e0 0xccff57ef40ffeaf0 0x37fe0fff81ff81e1 0x9bff07ffc0ffc0f0

def z321 : W := mkw 0x07815374636c6bdc 0x03c0a9ba31b635ee 0xff81fffc7ffc7fff 0xffc0fffe3ffe3fff

def z322 : W := mkw 0x0032bca95c000000 0x00195e54ae000000 0x3dfffffffe000000 0x1effffffff000000

def z323 : W := mkw 0x8bffee8819db7c22 0x45fff7440cedbe11 0x7bffff8031fffe66 0xbdffffc018ffff33

def z324 : W := mkw 0x8befee1001fb7f54 0x45f7f70800fdbfaa 0xfbfffe0001ffffff 0xfdffff0000ffffff

def z325 : W := mkw 0x0380015001602b54 0x01c000a800b015aa 0xe78001f001e07fff 0xf3c000f800f03fff

def z326 : W := mkw 0x4de7fc217c000000 0x26f3fe10be000000 0x39fffe007e000000 0x1cffff003f000000

def z327 : W := mkw 0xdff7ffeb7c097c00 0x6ffbfff5be04be00 0x3dfffffffe007e00 0x1effffffff003f00

def z328 : W := mkw 0x5876ac8b1c000000 0x2c3b56458e000000 0x3d7f8f8ffe000000 0x1ebfc7c7ff000000

def z329 : W := mkw 0x0200000000002a14 0x010000000000150a 0xc000000000007e1e 0x6000000000003f0f

def z330 : W := mkw 0x301237ffc62dc7f8 0x98091bffe316e3fc 0xbe867fffce7fcff9 0xdf433fffe73fe7fc

def z331 : W := mkw 0x0000000000000000 0x0000000000000000 0xae00000040004199 0x57000000200020cc

def z332 : W := mkw 0x8fefff6061db7c00 0x47f7ffb030edbe00 0x3ffffff071fffe00 0x1ffffff838ffff00

def z333 : W := mkw 0x0018028c029c50aa 0x000c0146014e2855 0xf778018c019c71ff 0xfbbc00c600ce38ff

def z334 : W := mkw 0x00388a8c009c50a0 0x001c4546004e2850 0x3f798f8c019c71e1 0x9fbcc7c600ce38f0

def z335 : W := mkw 0x59f7ec8b1c000000 0x2cfbf6458e000000 0x39fffe0f8e000000 0x1cffff07c7000000

def z336 : W := mkw 0x5dd775eb64000000 0x2eebbaf5b2000000 0x35fe71ff80000000 0x1aff38ffc0000000

def z337 : W := mkw 0x0781517061602b54 0x03c0a8b830b015aa 0x4181f1f031e03e66 0xa0c0f8f818f01f33

def z338 : W := mkw 0x105c008a00920020 0x882e004500490010 0x0078000000000000 0x003c000000000000

def z339 : W := mkw 0x4e23fc217c002a14 0x2711fe10be00150a 0xc801fe007e007e1e 0x6400ff003f003f0f

def z340 : W := mkw 0x105c01de80b681e0 0x882e00ef405b40f0 0x147e01ff801f81e1 0x8a3f00ffc00fc0f0

def z341 : W := mkw 0x20022614822dc798 0x1001130a4116e3cc 0xba867e00007fcf99 0x5d433f00003fe7cc

def z342 : W := mkw 0x0781414021402844 0x03c0a0a010a01422 0xef018180718071ff 0xf780c0c038c038ff

def z343 : W := mkw 0x0180117041600350 0x00c008b820b001a8 0xaf8071f041e04ff9 0xd7c038f820f027fc

def z344 : W := mkw 0x00288a04029c50aa 0x00144502014e2855 0xfb798e00019c71ff 0xfdbcc70000ce38ff

def z345 : W := mkw 0x8beffe3041fb7f10 0x45f7ff1820fdbf88 0xbffffe7041ffff99 0x5fffff3820ffffcc

def z346 : W := mkw 0x11c4014201420040 0x88e200a100a10020 0x0000000000000000 0x0000000000000000

def z347 : W := mkw 0x20023431c4218710 0x10011a18e210c388 0x3c867e7fce638e00 0x1e433f3fe731c700

def z348 : W := mkw 0x101001ca00000000 0x080800e500000000 0x040001ff80000000 0x020000ffc0000000

def z349 : W := mkw 0x0208021403fc7bfe 0x0104010a01fe3dff 0xc200000001fc7fff 0xe100000000fe3fff

def z350 : W := mkw 0x8bffee8c01df7ca0 0x45fff74600efbe50 0x3fffff8c01ffffe1 0x9fffffc600fffff0

def z351 : W := mkw 0xabc77635c76fef98 0x55e3bb1ae3b7f7cc 0xbe867e7fce7fcf99 0x5f433f3fe73fe7cc

def z352 : W := mkw 0x20023625c60dc698 0x10011b12e306e34c 0x98067e0fce1fce18 0x4c033f07e70fe70c

def z353 : W := mkw 0x00288a0000985000 0x00144500004c2800 0xff798f80719c71ff 0xffbcc7c038ce38ff

def z354 : W := mkw 0x5c77fcab7c000000 0x2e3bfe55be000000 0x187ffe0ffe000000 0x0c3fff07ff000000

def z355 : W := mkw 0xa86ebe35c6bfd798 0x54375f1ae35febcc 0xbefe7e7fce7fcf99 0x5f7f3f3fe73fe7cc

def z356 : W := mkw 0x4822ac011c000000 0x241156008e000000 0x00000e000e000000 0x0000070007000000

def z357 : W := mkw 0x20001234c22dc798 0x1000091a6116e3cc 0xae807070407fcf99 0x57403838203fe7cc

def z358 : W := mkw 0x0018028c1a9c50aa 0x000c01460d4e2855 0xc600018c7f9c71ff 0xe30000c63fce38ff

def z359 : W := mkw 0x11dc01ce01d600e0 0x88ee00e700eb0070 0x3778018c019c01e1 0x9bbc00c600ce00f0

def z360 : W := mkw 0xd87eae8b1c9b5400 0x6c3f57458e4daa00 0x107e0e0f8e1f8000 0x083f0707c70fc000

def z361 : W := mkw 0x2002240184018400 0x10011200c200c200 0x0006000380038000 0x00030001c001c000

def z362 : W := mkw 0x0200103041602b54 0x0100081820b015aa 0xee80707041e07fff 0xf740383820f03fff

def z363 : W := mkw 0x0000103040200310 0x0000081820100188 0x8400007040000199 0x42000038200000cc

def z364 : W := mkw 0x0200001001602b54 0x0100000800b015aa 0xc200000001e07fff 0xe100000000f03fff

def z365 : W := mkw 0x17d551fa61602b54 0x0beaa8fd30b015aa 0xfffff1fff1e07fff 0xfffff8fff8f03fff

def z366 : W := mkw 0x0180014000000000 0x00c000a000000000 0x258001f000000000 0x12c000f800000000

def z367 : W := mkw 0x00308a8c1a0c4088 0x001845460d062044 0xbf798f8c7e1c4199 0x5fbcc7c63f0e20cc

def z368 : W := mkw 0x8208000001d23800 0x4104000000e91c00 0x0000000001803000 0x0000000000c01800

def z369 : W := mkw 0x0000102144000000 0x00000810a2000000 0x0400007fce000000 0x0200003fe7000000

def z370 : W := mkw 0x15d551ea60000000 0x0aeaa8f530000000 0x3dfff1fff0000000 0x1efff8fff8000000

def z371 : W := mkw 0x5df7fdeb7c000000 0x2efbfef5be000000 0x0979ff807e000000 0x04bcffc03f000000

def z372 : W := mkw 0x11fc89de99f691e2 0x88fe44ef4cfb48f1 0x77ff81ffb1ffb1e7 0xbbffc0ffd8ffd8f3

def z373 : W := mkw 0x8200020000097c00 0x410001000004be00 0x0000000000007e00 0x0000000000003f00

def z374 : W := mkw 0x541001ca38000000 0x2a0800e51c000000 0x0000018030000000 0x000000c018000000

def z375 : W := mkw 0x11dc01de81f681e0 0x88ee00ef40fb40f0 0xffff81fff1fff1ff 0xffffc0fff8fff8ff

def z376 : W := mkw 0x21ce3635c7ffc798 0x10e71b1ae3ffe3cc 0xbffe7e7fcfffcf99 0x5fff3f3fe7ffe7cc

def z377 : W := mkw 0x7dc77573e4218710 0x3ee3bab9f210c388 0x0086707380638e00 0x00433839c031c700

def z378 : W := mkw 0x5df7ffeb7e08500a 0x2efbfff5bf042805 0xfdfffffffe00701e 0x7effffffff00380f

def z379 : W := mkw 0xdfefff6365db7c00 0x6ff7ffb1b2edbe00 0x3bfffe7381fffe00 0x1dffff39c0ffff00

def z380 : W := mkw 0x01800154816481c0 0x00c000aa40b240e0 0x378601ff81ff81e1 0x9bc300ffc0ffc0f0

def z381 : W := mkw 0x11fc8bce1a9c50aa 0x08fe45e70d4e2855 0xffff8fffff9c71ff 0xffffc7ffffce38ff

def z382 : W := mkw 0x7dc77777e62dc798 0x3ee3bbbbf316e3cc 0xbe867e7fce7fcf99 0x5f433f3fe73fe7cc

def z383 : W := mkw 0x20022615862dc798 0x1001130ac316e3cc 0x92060e0f8e7fcf99 0x49030707c73fe7cc

def z384 : W := mkw 0x0789537463fc7bfe 0x03c4a9ba31fe3dff 0xef81f1f071fc7fff 0xf7c0f8f838fe3fff

def z385 : W := mkw 0x00000204020c4088 0x0000010201062044 0xff018f8c7f9c71ff 0xff80c7c63fce38ff

def z386 : W := mkw 0x5fc7757365602b54 0x2fe3bab9b2b015aa 0x0086707380600e00 0x00433839c0300700

def z387 : W := mkw 0x17dd41dea1f6a9e4 0x8beea0ef50fb54f2 0x77ff81ffb1ffb1e7 0xbbffc0ffd8ffd8f3

def z388 : W := mkw 0x2002362146094618 0x10011b10a304a30c 0xba867e004e7fce18 0x5d433f00273fe70c

def z389 : W := mkw 0x20389abddebcd3ba 0x101c4d5eef5e69dd 0xff798fffff9c71ff 0xffbcc7ffffce38ff

def z390 : W := mkw 0x8a2bee0000997c00 0x4515f700004cbe00 0x3b79fe00019c7e00 0x1dbcff0000ce3f00

def z391 : W := mkw 0x8bcf660001db7c00 0x45e7b30000edbe00 0x0286700001fffe00 0x0143380000ffff00

def z392 : W := mkw 0x0000015000200140 0x000000a8001000a0 0x040001f0000001e1 0x820000f8000000f0

def z393 : W := mkw 0x0601517060202b54 0x0300a8b8301015aa 0xcc01f1f070007fff 0xe600f8f838003fff

def z394 : W := mkw 0x887eae8c1a9f54aa 0x443f57460d4faa55 0xff7f8f8c7f9ff1ff 0xffbfc7c63fcff8ff

def z395 : W := mkw 0x5dfdc9ca39d20060 0xaefee4e51ce90030 0x0179818031800060 0x80bcc0c018c00030

def z396 : W := mkw 0x2008021482bdd7ba 0x1004010a415eebdd 0xc200000001ffffff 0xe100000000ffffff

def z397 : W := mkw 0x20023635c62dc798 0x10011b1ae316e3cc 0x94060e7fce1f8199 0x4a03073fe70fc0cc

def z398 : W := mkw 0x0030888c1a0400aa 0x001844460d020055 0xfd798f8c7e0001ff 0xfebcc7c63f0000ff

def z399 : W := mkw 0x000002000208500a 0x0000010001042805 0xc00000000000701e 0x600000000000380f

def z400 : W := mkw 0x00208a0000085000 0x0010450000042800 0x08018e0000007000 0x0400c70000003800

def z401 : W := mkw 0x5ff7fdeb7c002a14 0x2ffbfef5be00150a 0xfdfffffffe007e1e 0x7effffffff003f0f

def z402 : W := mkw 0x0038888818901022 0x001c44440c480811 0xef798180718071ff 0xf7bcc0c038c038ff

def z403 : W := mkw 0x11d401ca00000000 0x08ea00e500000000 0x0178018000000000 0x00bc00c000000000

def z404 : W := mkw 0x20001235c62dc798 0x1000091ae316e3cc 0x8600007fce7fcf99 0x4300003fe73fe7cc

def z405 : W := mkw 0x0781517061602b54 0x03c0a8b830b015aa 0x278071f001e00fe1 0x93c038f800f007f0

def z406 : W := mkw 0x2032bebdde2dc798 0x10195f5eef16e3cc 0xbffffffffe7fcf99 0x5fffffffff3fe7cc

def z407 : W := mkw 0x541011fb7c200354 0x2a0808fdbe1001aa 0xc40001fffe0001ff 0xe20000ffff0000ff

def z408 : W := mkw 0x0601502060002a14 0x0300a8103000150a 0x0000700000000e00 0x0000380000000700

def z409 : W := mkw 0x5df7fdfffc2481e0 0xaefbfefffe1240f0 0x3dfffffffe0001e1 0x9effffffff0000f0

def z410 : W := mkw 0x8bc7640001432c00 0x45e3b20000a19600 0x2b87f00001e3fe00 0x15c3f80000f1ff00

def z411 : W := mkw 0x20022605860dc488 0x10011302c306e244 0x3a867e0f8e7fce00 0x1d433f07c73fe700

def z412 : W := mkw 0x105c009e80b681a0 0x882e004f405b40d0 0x36fe007f807f8181 0x1b7f003fc03fc0c0

def z413 : W := mkw 0x0781516061402800 0x03c0a8b030a01400 0x2f81f1f071e07e00 0x17c0f8f838f03f00

def z414 : W := mkw 0x17fddbfefbfefbfe 0x8bfeedff7dff7dff 0xffffffffffffffff 0xffffffffffffffff

def z415 : W := mkw 0x4c23fe217e08500a 0x2611ff10bf042805 0xc801fe007e00701e 0x6400ff003f00380f

def z416 : W := mkw 0x8389420001db7c00 0x41c4a10000edbe00 0x2b81f00001fffe00 0x15c0f80000ffff00

def z417 : W := mkw 0x01cc015001f20140 0x00e600a800f900a0 0x37fe01f001ff81e1 0x9bff00f800ffc0f0

def z418 : W := mkw 0x2000020002094618 0x100001000104a30c 0x8000000000004e18 0x400000000000270c

def z419 : W := mkw 0x0000000000000000 0x0000000000000000 0x3c000e0c4e000000 0x1e00070627000000

def z420 : W := mkw 0x0018008c009400a0 0x000c0046004a0050 0x1078000c001c0000 0x083c0006000e0000

def z421 : W := mkw 0x11c40156816681c0 0x88e200ab40b340e0 0x3686007f807f8181 0x1b43003fc03fc0c0

def z422 : W := mkw 0xdfffffef7fdf7caa 0x6ffffff7bfefbe55 0xffffffffffffffff 0xffffffffffffffff

def z423 : W := mkw 0x004c000000920000 0x0026000000490000 0x107e0000001f8000 0x083f0000000fc000

def z424 : W := mkw 0x15dd51fee1f681e0 0x8aeea8ff70fb40f0 0x3ffff1fff1ff81e1 0x9ffff8fff8ffc0f0

def z425 : W := mkw 0x8bedc80001d23800 0x45f6e40000e91c00 0x33ff800001ffb000 0x19ffc00000ffd800

def z426 : W := mkw 0x0002362144094400 0x00011b10a204a200 0x3e867e7fce7fce00 0x1f433f3fe73fe700

def z427 : W := mkw 0x8bcf640001d32c00 0x45e7b20000e99600 0x33fe700001ff8e00 0x19ff380000ffc700

def z428 : W := mkw 0x27837571e561af54 0x13c1bab8f2b0d7aa 0xef87f1f3f1e3ffff 0xf7c3f8f9f8f1ffff

def z429 : W := mkw 0x8a6fee00009b7c00 0x4537f700004dbe00 0x187ffe00001ffe00 0x0c3fff00000fff00

def z430 : W := mkw 0x5874888a18000000 0x2c3a44450c000000 0x0078000000000000 0x003c000000000000

def z431 : W := mkw 0x11dc01ce809680a0 0x88ee00e7404b4050 0x35fe01ff801f8000 0x1aff00ffc00fc000

def z432 : W := mkw 0xdffdc9ca39d23800 0x6ffee4e51ce91c00 0x0179818031803000 0x00bcc0c018c01800

def z433 : W := mkw 0x5dfffdeb7dd20000 0x2efffef5bee90000 0x3fffffffffff8000 0x1fffffffffffc000

def z434 : W := mkw 0x8befee0001db7c00 0x45f7f70000edbe00 0xffffff8071ffffff 0xffffffc038ffffff

def z435 : W := mkw 0x0000020002084008 0x0000010001042004 0x88000e004e004018 0x440007002700200c

def z436 : W := mkw 0x00023435c4248180 0x00011a1ae21240c0 0x3e867e7fce7f8181 0x1f433f3fe73fc0c0

def z437 : W := mkw 0x1000015280208140 0x880000a9401040a0 0x0000007380000000 0x00000039c0000000

def z438 : W := mkw 0x0200000001402800 0x0100000000a01400 0x0200000001e07e00 0x0100000000f03f00

def z439 : W := mkw 0x5df7ffeb7c094400 0x2efbfff5be04a200 0x3ffffffffe7fce00 0x1fffffffff3fe700

def z440 : W := mkw 0x305e36bfc6bfc7b8 0x982f1b5fe35fe3dc 0xbefe7e7fce7fcf99 0x5f7f3f3fe73fe7cc

def z441 : W := mkw 0xabefee0587dffc88 0x55f7f702c3effe44 0x3bfffe0f8ffffe00 0x1dffff07c7ffff00

def z442 : W := mkw 0x8befec0001d33c00 0x45f7f60000e99e00 0x01fff00001e3be00 0x00fff80000f1df00

def z443 : W := mkw 0x2002362146094618 0x10011b10a304a30c 0xbc867e7fce004e18 0x5e433f3fe700270c

def z444 : W := mkw 0x003abead5e9c50aa 0x001d5f56af4e2855 0xffffffffff9c71ff 0xffffffffffce38ff

def z445 : W := mkw 0x9befef5281fbfd40 0xcdf7f7a940fdfea0 0x3bfffe7381fffe00 0x1dffff39c0ffff00

def z446 : W := mkw 0x0000102040000210 0x0000081020000108 0x8800700040004e18 0x440038002000270c

def z447 : W := mkw 0x0de7fd6060000000 0x06f3feb030000000 0x3dfffff070000000 0x1efffff838000000

def z448 : W := mkw 0x5dc7756364000000 0x2ee3bab1b2000000 0x2d87f1f3f0000000 0x16c3f8f9f8000000

def z449 : W := mkw 0x20023635c62dc798 0x10011b1ae316e3cc 0x82867073807fcf99 0x41433839c03fe7cc

def z450 : W := mkw 0x0381415001602940 0x01c0a0a800b014a0 0x2f81f1f001e07fe1 0x97c0f8f800f03ff0

def z451 : W := mkw 0x00388a8818985000 0x001c45440c4c2800 0x3f798f8c7f9c7000 0x1fbcc7c63fce3800

def z452 : W := mkw 0x00001234422c4398 0x0000091a211621cc 0xbe807e7c4e7c4f99 0x5f403f3e273e27cc

def z453 : W := mkw 0x0201400000002800 0x0100a00000001400 0x0801f00000007e00 0x0400f80000003f00

def z454 : W := mkw 0x886eae00009b5400 0x44375700004daa00 0x3afe7e00007fce00 0x1d7f3f00003fe700

def z455 : W := mkw 0x7876bebfde2dc798 0x3c3b5f5fef16e3cc 0xbefe7e7fce7fcf99 0x5f7f3f3fe73fe7cc

def z456 : W := mkw 0x0008001481f681e0 0x8004000a40fb40f0 0x3686007f81ff81e1 0x9b43003fc0ffc0f0

def z457 : W := mkw 0x07b9cbcc3bdc78ee 0x03dce5e61dee3c77 0xff798f8c7f9c71ff 0xffbcc7c63fce38ff

def z458 : W := mkw 0x987eae8e809fd4a0 0xcc3f5747404fea50 0x107e0e0f801f8000 0x083f0707c00fc000

def z459 : W := mkw 0x8a23ee001a097c0a 0x4511f7000d04be05 0xc801fe007e007e1e 0x6400ff003f003f0f

def z460 : W := mkw 0x01dc008c01d600a0 0x00ee004600eb0050 0x37fe018c01ff81e1 0x9bff00c600ffc0f0

def z461 : W := mkw 0x141011fee02483f4 0x8a0808ff701241fa 0xc40001fff00001ff 0xe20000fff80000ff

def z462 : W := mkw 0x0000000480048080 0x0000000240024040 0x1006000f801f8000 0x08030007c00fc000

def z463 : W := mkw 0x89efee00009b5400 0x44f7f700004daa00 0x39fffe00001f8000 0x1cffff00000fc000

def z464 : W := mkw 0x7dffffffffffc7f8 0xbeffffffffffe3fc 0xbfffffffffffcff9 0xdfffffffffffe7fc

def z465 : W := mkw 0x00388a8c1a9c50aa 0x001c45460d4e2855 0x37780f8c0f9c01e1 0x9bbc07c607ce00f0

def z466 : W := mkw 0x5dfffdeb7dd20060 0xaefffef5bee90030 0x3dffffffff800060 0x9effffffffc00030

def z467 : W := mkw 0x8ba3ee0001497c00 0x45d1f70000a4be00 0x2b81fe0001e07e00 0x15c0ff0000f03f00

def z468 : W := mkw 0x0030888818000000 0x001844440c000000 0xff798f8c7f8071ff 0xffbcc7c63fc038ff

def z469 : W := mkw 0x11de27de81ffc5e0 0x88ef13ef40ffe2f0 0x3ffe7fff81ffcfe1 0x9fff3fffc0ffe7f0

def z470 : W := mkw 0x201236bdde2dc7ba 0x10091b5eef16e3dd 0xfe867ffffe7fcfff 0xff433fffff3fe7ff

def z471 : W := mkw 0x8befef5001fb7d40 0x45f7f7a800fdbea0 0x3ffffff001ffffe1 0x9ffffff800fffff0

def z472 : W := mkw 0x5df7edcb3c000000 0x2efbf6e59e000000 0x117f8f8fbe000000 0x08bfc7c7df000000

def z473 : W := mkw 0x0581517060200310 0x02c0a8b830100188 0xaf81f1f070604f99 0x57c0f8f8383027cc

def z474 : W := mkw 0x820a260001db7c00 0x4105130000edbe00 0x3a867e0001fffe00 0x1d433f0000ffff00

def z475 : W := mkw 0x0781517061602b54 0x03c0a8b830b015aa 0x2b81f07001e07e00 0x15c0f83800f03f00

def z476 : W := mkw 0x0000001000200310 0x0000000800100188 0x8200000000604f99 0x41000000003027cc

def z477 : W := mkw 0x01cc000001d20000 0x00e6000000e90000 0x0178000001800000 0x00bc000000c00000

def z478 : W := mkw 0x101001ca00000060 0x880800e500000030 0x0000018000000060 0x800000c000000030

def z479 : W := mkw 0xdfc7756365432c00 0x6fe3bab1b2a19600 0x0086707380638e00 0x00433839c031c700

def z480 : W := mkw 0x0000000000000000 0x0000000000000000 0x2b01800001807000 0x1580c00000c03800

def z481 : W := mkw 0x203abebddebdd7ba 0x101d5f5eef5eebdd 0xbefe7e7fce7fcf99 0x5f7f3f3fe73fe7cc

def z482 : W := mkw 0x0038888818901022 0x001c44440c480811 0x4179818031803066 0xa0bcc0c018c01833

def z483 : W := mkw 0x00388a9c9abcd1aa 0x001c454e4d5e68d5 0xffff8ffffffff1ff 0xffffc7fffffff8ff

def z484 : W := mkw 0x00080204029c50aa 0x00040102014e2855 0xfe000e0c4f9c71ff 0xff00070627ce38ff

def z485 : W := mkw 0x9bffefde9bfffdea 0xcdfff7ef4dfffef5 0xffffffffffffffff 0xffffffffffffffff

def z486 : W := mkw 0x8bc5400001422800 0x45e2a00000a11400 0x0000000000000000 0x0000000000000000

def z487 : W := mkw 0x0028880000901000 0x0014440000480800 0x0179800001803000 0x00bcc00000c01800

def z488 : W := mkw 0x8a6eae0001db7c00 0x4537570000edbe00 0x127e0e0001fffe00 0x093f070000ffff00

def z489 : W := mkw 0x0038888818901022 0x001c44440c480811 0x7d798f8c7f803066 0xbebcc7c63fc01833

def z490 : W := mkw 0x0000020000094400 0x000001000004a200 0x02000000007fce00 0x01000000003fe700

def z491 : W := mkw 0x9bffefca01db7c00 0x4dfff7e500edbe00 0x3fffffff81fffe00 0x1fffffffc0ffff00

def z492 : W := mkw 0x003aae8c1a9d54aa 0x001d57460d4eaa55 0xffffff8c7fffffff 0xffffffc63fffffff

def z493 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z494 : W := mkw 0x5dd775eb7c000000 0x2eebbaf5be000000 0x048671fffe000000 0x024338ffff000000

def z495 : W := mkw 0x11d401da01600140 0x08ea00ed00b000a0 0x37fe01ff81e001e1 0x9bff00ffc0f000f0

def z496 : W := mkw 0x11fc8bce1bde50ea 0x88fe45e70def2875 0xff798f8c7f9c71ff 0xffbcc7c63fce38ff

def z497 : W := mkw 0x19f7edca00000000 0x0cfbf6e500000000 0x3dffffff80000000 0x1effffffc0000000

def z498 : W := mkw 0x0781502061402a14 0x03c0a81030a0150a 0xeb81f00071e07e1e 0x75c0f80038f03f0f

def z499 : W := mkw 0x93dc03de81fffde0 0xc9ee01ef40fffef0 0x37fe01ff81ffffe1 0x9bff00ffc0fffff0

def z500 : W := mkw 0x17dd51fa61f22b74 0x8beea8fd30f915ba 0xeff9f1f071e07fff 0xf7fcf8f838f03fff

def z501 : W := mkw 0x0601503060202b14 0x0300a8183010158a 0xee81f07070607f9f 0x7740f83838303fcf

def z502 : W := mkw 0x0000000000000000 0x0000000000000000 0x27000180018001e1 0x938000c000c000f0

def z503 : W := mkw 0x101001de9a2481ea 0x880800ef4d1240f5 0xc40001fffe0001ff 0xe20000ffff0000ff

def z504 : W := mkw 0x5ff5d9fa79602b54 0x2ffaecfd3cb015aa 0xeff9f1f071e07fff 0xf7fcf8f838f03fff

def z505 : W := mkw 0x0583756164000000 0x02c1bab0b2000000 0x3d87fffffe000000 0x1ec3ffffff000000

def z506 : W := mkw 0x0000000000000000 0x0000000000000000 0x3486007f80000000 0x1a43003fc0000000

def z507 : W := mkw 0x5fc7757365602b54 0x2fe3bab9b2b015aa 0xef87f1f3f1e07fff 0xf7c3f8f9f8f03fff

def z508 : W := mkw 0x5dc77573e5628140 0xaee3bab9f2b140a0 0x0086707380638000 0x00433839c031c000

def z509 : W := mkw 0x107c8a8e9a9ed0aa 0x883e45474d4f6855 0x107e0e0f8e1f8000 0x083f0707c70fc000

def z510 : W := mkw 0xdffffffffdfffde0 0xeffffffffefffef0 0x3fffffffffffffe1 0x9ffffffffffffff0

def z511 : W := mkw 0xabc77431c563af10 0x55e3ba18e2b1d788 0x0086707380638e00 0x00433839c031c700

def z512 : W := mkw 0x20023435c6248398 0x10011a1ae31241cc 0xbc867e7fce000199 0x5e433f3fe70000cc

def z513 : W := mkw 0x82288a0001db7c00 0x4114450000edbe00 0x3b798e0001fffe00 0x1dbcc70000ffff00

def z514 : W := mkw 0x11fc8bde81fed1e0 0x88fe45ef40ff68f0 0x3fff8fff81fff1e1 0x9fffc7ffc0fff8f0

def z515 : W := mkw 0x11d401de816681e0 0x88ea00ef40b340f0 0x048601ff806381e1 0x824300ffc031c0f0

def z516 : W := mkw 0x20001035c6248398 0x1000081ae31241cc 0xae80707fce604f99 0x5740383fe73027cc

def z517 : W := mkw 0x5c33fdeb7c000000 0x2e19fef5be000000 0x0c01fffffe000000 0x0600ffffff000000

def z518 : W := mkw 0xabefee1483ffff98 0x55f7f70a41ffffcc 0xbbfffe0001ffff99 0x5dffff0000ffffcc

def z519 : W := mkw 0x0400117060200354 0x020008b8301001aa 0xef0181f0718071ff 0xf780c0f838c038ff

def z520 : W := mkw 0x5010008b1c000000 0x280800458e000000 0x0000000f8e000000 0x00000007c7000000

def z521 : W := mkw 0x0008000001d20060 0x8004000000e90030 0x0000000001800060 0x8000000000c00030

def z522 : W := mkw 0x00308a8c1a0c50aa 0x001845460d062855 0xcc018f8c7e0071ff 0xe600c7c63f0038ff

def z523 : W := mkw 0x203aae8d9e9dd4aa 0x101d5746cf4eea55 0x107e0e0f8e1f8000 0x083f0707c70fc000

def z524 : W := mkw 0x59feaddf9df681e0 0xacff56efcefb40f0 0x37fe0fff8fff81e1 0x9bff07ffc7ffc0f0

def z525 : W := mkw 0x9bfdc9ca01d23860 0xcdfee4e500e91c30 0x0179818001803060 0x80bcc0c000c01830

def z526 : W := mkw 0x07a1db707b687b5e 0x03d0edb83db43daf 0xef81fff07fe07fff 0xf7c0fff83ff03fff

def z527 : W := mkw 0x20023631c429c710 0x10011b18e214e388 0x3a867e73807fce00 0x1d433f39c03fe700

def z528 : W := mkw 0x89eeae0001db5400 0x44f7570000edaa00 0x33fe0e0001ff8000 0x19ff070000ffc000

def z529 : W := mkw 0x01cc001481f681e0 0x80e6000a40fb40f0 0x33fe000001ff81e1 0x99ff000000ffc0f0

def z530 : W := mkw 0x5df7fdfffc248180 0x2efbfefffe1240c0 0x3ffffffffe7f8181 0x1fffffffff3fc0c0

def z531 : W := mkw 0x00208a001a08500a 0x001045000d042805 0x00000e000e000000 0x0000070007000000

def z532 : W := mkw 0x5dc5414220000000 0x2ee2a0a110000000 0x0000000000000000 0x0000000000000000

def z533 : W := mkw 0x0018028c029c40a8 0x000c0146014e2054 0xbf780f8c4f9c41f9 0xdfbc07c627ce20fc

def z534 : W := mkw 0x2000102146000218 0x10000810a300010c 0x800000004e000018 0x400000002700000c

def z535 : W := mkw 0xcfeffe217ddb7c00 0x67f7ff10beedbe00 0x3bfffe007ffffe00 0x1dffff003fffff00

def z536 : W := mkw 0x0600117061602b54 0x030008b830b015aa 0xc60001f071e07fff 0xe30000f838f03fff

def z537 : W := mkw 0x0381401001602b54 0x01c0a00800b015aa 0xeb81f00001e07fff 0xf5c0f80000f03fff

def z538 : W := mkw 0x8befee0403df7c88 0x45f7f70201efbe44 0xbffffe0c4fffff99 0x5fffff0627ffffcc

def z539 : W := mkw 0x179151fee164abf4 0x8bc8a8ff70b255fa 0xef81f1fff1e07fff 0xf7c0f8fff8f03fff

def z540 : W := mkw 0x0000000402040088 0x0000000201020044 0x8400000c4e000199 0x42000006270000cc

def z541 : W := mkw 0x541011ef7e0400aa 0x2a0808f7bf020055 0xc40001fffe0001ff 0xe20000ffff0000ff

def z542 : W := mkw 0x741237fffe2dc798 0x3a091bffff16e3cc 0xbe867ffffe7fcf99 0x5f433fffff3fe7cc

def z543 : W := mkw 0x0581516060000000 0x02c0a8b030000000 0xef81f1f0718071ff 0xf7c0f8f838c038ff

def z544 : W := mkw 0x5dffffeb7c985000 0x2efffff5be4c2800 0x3fffffffff9c7000 0x1fffffffffce3800

def z545 : W := mkw 0x0866ac0000000000 0x0433560000000000 0x107e0e0000000000 0x083f070000000000

def z546 : W := mkw 0x8846240000030400 0x4423120000018200 0x0006000000038000 0x000300000001c000

def z547 : W := mkw 0x9bc765528163ad40 0xcde3b2a940b1d6a0 0x0086707380638e00 0x00433839c031c700

def z548 : W := mkw 0x19ffedde81f681e0 0x8cfff6ef40fb40f0 0x3fffffff81ff81e1 0x9fffffffc0ffc0f0

def z549 : W := mkw 0x0781517061602b54 0x03c0a8b830b015aa 0x2d81f1f070600e00 0x16c0f8f838300700

def z550 : W := mkw 0x5df7fdfb7c200354 0x2efbfefdbe1001aa 0xfdfffffffe0001ff 0xfeffffffff0000ff

def z551 : W := mkw 0x0400117060200354 0x020008b8301001aa 0xee8071f070604fff 0xf74038f8383027ff

def z552 : W := mkw 0x5df5d9ea78000000 0x2efaecf53c000000 0x2df9f1f070000000 0x16fcf8f838000000

def z553 : W := mkw 0x80080200009b5400 0x40040100004daa00 0x00000000001f8000 0x00000000000fc000

def z554 : W := mkw 0x2022be35de2dd79a 0x10115f1aef16ebcd 0xfe87fe7ffe7fff9f 0x7f43ff3fff3fffcf

def z555 : W := mkw 0x5df7fdfbfd628140 0xaefbfefdfeb140a0 0x3dfffffffe638000 0x1effffffff31c000

def z556 : W := mkw 0x4fa3fd717d602b54 0x27d1feb8beb015aa 0xef81fff07fe07fff 0xf7c0fff83ff03fff

def z557 : W := mkw 0x0823ec0000000000 0x0411f60000000000 0x0801fe0000000000 0x0400ff0000000000

def z558 : W := mkw 0x101001de802481e0 0x880800ef401240f0 0x368601ff807f81e1 0x9b4300ffc03fc0f0

def z559 : W := mkw 0x11fc89de99f681e0 0x88fe44ef4cfb40f0 0x3fff8fffffff81e1 0x9fffc7ffffffc0f0

def z560 : W := mkw 0x0781516061402a54 0x03c0a8b030a0152a 0xc901f18071807e7e 0xe480f8c038c03f3f

def z561 : W := mkw 0x11d401de802481e0 0x88ea00ef401240f0 0x35fe01ff800001e1 0x9aff00ffc00000f0

def z562 : W := mkw 0x0381400001402800 0x01c0a00000a01400 0x0101800001803000 0x0080c00000c01800

def z563 : W := mkw 0x07cd517061f22b54 0x03e6a8b830f915aa 0xfffff1f071ffffff 0xfffff8f838ffffff

def z564 : W := mkw 0x4c03742164000000 0x2601ba10b2000000 0x0000700000000000 0x0000380000000000

def z565 : W := mkw 0x11dc03de83fed1ea 0x88ee01ef41ff68f5 0xf7fe01ff81fff1ff 0xfbff00ffc0fff8ff

def z566 : W := mkw 0x886c880000921000 0x4436440000490800 0x0078000000000000 0x003c000000000000

def z567 : W := mkw 0x0200001001602b54 0x0100000800b015aa 0x0000000000600e00 0x0000000000300700

def z568 : W := mkw 0x0010008818000022 0x000800440c000011 0x4000018030000066 0xa00000c018000033

def z569 : W := mkw 0x20000204820dc488 0x100001024106e244 0x00000000001f8000 0x00000000000fc000

def z570 : W := mkw 0x105c009e81f681e0 0x882e004f40fb40f0 0x127e000f81ff81e1 0x893f0007c0ffc0f0

def z571 : W := mkw 0x8208021001fb7f54 0x4104010800fdbfaa 0xc200000001ffffff 0xe100000000ffffff

def z572 : W := mkw 0x0020880018001002 0x001044000c000801 0x4001800030003006 0x2000c00018001803

def z573 : W := mkw 0x0008000001d20000 0x0004000000e90000 0x0200000001ff8000 0x0100000000ffc000

def z574 : W := mkw 0x8bedca0001da7800 0x45f6e50000ed3c00 0x3b798e00019c7000 0x1dbcc70000ce3800

def z575 : W := mkw 0x11cc015281f28140 0x88e600a940f940a0 0x33fe007381ff8000 0x19ff0039c0ffc000

def z576 : W := mkw 0x5df7fdfb7c200310 0x2efbfefdbe100188 0xbffffffffe604f99 0x5fffffffff3027cc

def z577 : W := mkw 0x20023435c4258790 0x10011a1ae212c3c8 0x3686707f807f8f81 0x1b43383fc03fc7c0

def z578 : W := mkw 0x0181400000000000 0x00c0a00000000000 0x2981f00000000000 0x14c0f80000000000

def z579 : W := mkw 0x0400116060000000 0x020008b030000000 0x040001f070000000 0x020000f838000000

def z580 : W := mkw 0xbbffffffc7fffff8 0xddffffffe3fffffc 0xbfffffffcffffff9 0xdfffffffe7fffffc

def z581 : W := mkw 0x7876ae8f9e0dc488 0x3c3b5747cf06e244 0x107e0e0f8e1f8000 0x083f0707c70fc000

def z582 : W := mkw 0xa86eae05869fd488 0x54375702c34fea44 0x107e0e0f8e1f8000 0x083f0707c70fc000

def z583 : W := mkw 0x5de7fd6364000000 0x2ef3feb1b2000000 0x39fffe7380000000 0x1cffff39c0000000

def z584 : W := mkw 0x0008000000900000 0x0004000000480000 0x33780000019c0000 0x19bc000000ce0000

def z585 : W := mkw 0x31c63573c5638750 0x98e31ab9e2b1c3a8 0x0086707380638e00 0x00433839c031c700

def z586 : W := mkw 0x0381400001402800 0x01c0a00000a01400 0x0080700000600e00 0x0040380000300700

def z587 : W := mkw 0x0000001001600140 0x0000000800b000a0 0x0200000001e001e1 0x8100000000f000f0

def z588 : W := mkw 0x0208001481f6abf4 0x8104000a40fb55fa 0xc200000001ffffff 0xe100000000ffffff

def z589 : W := mkw 0x107c8a8e9a9ed0aa 0x883e45474d4f6855 0xff7f8f8fff9ff1ff 0xffbfc7c7ffcff8ff

def z590 : W := mkw 0x00022614802dc580 0x0001130a4016e2c0 0x3e867e7f807fcf81 0x1f433f3fc03fe7c0

def z591 : W := mkw 0x02388a9c1bfc7bfe 0x011c454e0dfe3dff 0xff798f8c7ffc7fff 0xffbcc7c63ffe3fff

def z592 : W := mkw 0x20023625c60dc488 0x10011b12e306e244 0x3c867e7fce1f8000 0x1e433f3fe70fc000

def z593 : W := mkw 0x8208021481fffde0 0xc104010a40fffef0 0x0200000001ffffe1 0x8100000000fffff0

def z594 : W := mkw 0x5df7ffef7e0c4088 0x2efbfff7bf062044 0xbffffffffe1c4199 0x5fffffffff0e20cc

def z595 : W := mkw 0x8fc7757061632f54 0x47e3bab830b197aa 0xef87f1f071e3ffff 0xf7c3f8f838f1ffff

def z596 : W := mkw 0x5dfffffffffed1ea 0xaeffffffffff68f5 0xfffffffffffff1ff 0xfffffffffffff8ff

def z597 : W := mkw 0x0639daac7a9c7abe 0x031ced563d4e3d5f 0xff79ff8c7f9c7fff 0xffbcffc63fce3fff

def z598 : W := mkw 0x541235eb7c000000 0x2a091af5be000000 0x3c867ffffe000000 0x1e433fffff000000

def z599 : W := mkw 0x0781517061602b54 0x03c0a8b830b015aa 0xc881f07070607e1e 0x6440f83838303f0f

def z600 : W := mkw 0x0010008c1a0400aa 0x000800460d020055 0xef01818c7f8071ff 0xf780c0c63fc038ff

def z601 : W := mkw 0xabeffe2147db7e18 0x55f7ff10a3edbf0c 0xbbfffe004ffffe18 0x5dffff0027ffff0c

def z602 : W := mkw 0x10388bde9abcd1ea 0x881c45ef4d5e68f5 0xff798fffff9c71ff 0xffbcc7ffffce38ff

def z603 : W := mkw 0x079951fc61f42bf4 0x03cca8fe30fa15fa 0xfff9f1fc71fc7fff 0xfffcf8fe38fe3fff

def z604 : W := mkw 0x00388a8c1a9c50aa 0x001c45460d4e2855 0xd8798e0c7e1c701e 0x6c3cc7063f0e380f

def z605 : W := mkw 0x6c23fe35fe2dc798 0x3611ff1aff16e3cc 0xbe87fe7ffe7fcf99 0x5f43ff3fff3fe7cc

def z606 : W := mkw 0x0000000400040080 0x0000000200020040 0x3600000c001c0181 0x1b000006000e00c0

def z607 : W := mkw 0x587eae8f1e9c50aa 0x2c3f57478f4e2855 0x107e0e0f8e1c0000 0x083f0707c70e0000

def z608 : W := mkw 0x8a2bee0001db7c00 0x4515f70000edbe00 0x0a01fe0001fffe00 0x0500ff0000ffff00

def z609 : W := mkw 0x0038888c1a9410aa 0x001c44460d4a0855 0xc579818c7f8031ff 0xe2bcc0c63fc018ff

def z610 : W := mkw 0x09f7ec8818000000 0x04fbf6440c000000 0x3dffff8c7e000000 0x1effffc63f000000

def z611 : W := mkw 0x11dc008e81d680a0 0x88ee004740eb4050 0x33fe000f81ff8000 0x19ff0007c0ffc000

def z612 : W := mkw 0x01ec8a0001da5000 0x00f6450000ed2800 0x3bff8e0001fff000 0x1dffc70000fff800

def z613 : W := mkw 0x0002240000010400 0x0001120000008200 0x0086700000638e00 0x004338000031c700

def z614 : W := mkw 0x0180014001400040 0x00c000a000a00020 0x0100018001800060 0x808000c000c00030

def z615 : W := mkw 0x9bffefca01db7c60 0xcdfff7e500edbe30 0x3bffff8001fffe60 0x9dffffc000ffff30

def z616 : W := mkw 0x0781516061402844 0x03c0a8b030a01422 0x6d81f1f071803066 0xb6c0f8f838c01833

def z617 : W := mkw 0x00308a881a08500a 0x001845440d042805 0xfd798f8c7e00701e 0x7ebcc7c63f00380f

def z618 : W := mkw 0x20023431c4218710 0x10011a18e210c388 0xae867073c063cf99 0x57433839e031e7cc

def z619 : W := mkw 0x0781517061602b54 0x03c0a8b830b015aa 0xc280707001e07fff 0xe140383800f03fff

def z620 : W := mkw 0x11dc01da01f20160 0x88ee00ed00f900b0 0x27f801f001e001e1 0x93fc00f800f000f0

def z621 : W := mkw 0x24023775e62dc7dc 0x12011bbaf316e3ee 0xfe867ffffe7fcfff 0xff433fffff3fe7ff

def z622 : W := mkw 0x8a3bee8c1a9d7caa 0x451df7460d4ebe55 0xff79ff8c7f9c7fff 0xffbcffc63fce3fff

def z623 : W := mkw 0x11dc01ca01d20060 0x88ee00e500e90030 0x33fe018001ff8060 0x99ff00c000ffc030

def z624 : W := mkw 0x20022615862dc588 0x1001130ac316e2c4 0x36860e7f8e7f8181 0x1b43073fc73fc0c0

def z625 : W := mkw 0x0002240000000000 0x0001120000000000 0x38867e0000000000 0x1c433f0000000000

def z626 : W := mkw 0x0fe7fd7061602b54 0x07f3feb830b015aa 0xfffffff071e07fff 0xfffffff838f03fff

def z627 : W := mkw 0x11cc015681f681e0 0x88e600ab40fb40f0 0x0286007381ff81e1 0x81430039c0ffc0f0

def z628 : W := mkw 0x0188015481f681e0 0x80c400aa40fb40f0 0x278001f001ff81e1 0x93c000f800ffc0f0

def z629 : W := mkw 0x0781414021402844 0x03c0a0a010a01422 0x0000000000000000 0x0000000000000000

def z630 : W := mkw 0x5876bcab5c000000 0x2c3b5e55ae000000 0x3cfe7e7fce000000 0x1e7f3f3fe7000000

def z631 : W := mkw 0x00080204029c50aa 0x00040102014e2855 0x00000000001c0000 0x00000000000e0000

def z632 : W := mkw 0x0200000001402844 0x0100000000a01422 0x4000000001803066 0xa000000000c01833

def z633 : W := mkw 0x305e268f869fc4a8 0x982f1347c34fe254 0x107e0e0f8e1f8000 0x083f0707c70fc000

def z634 : W := mkw 0x4c23fc217c000000 0x2611fe10be000000 0x3c87fe7ffe000000 0x1e43ff3fff000000

def z635 : W := mkw 0x31dc11ffc7f683f8 0x98ee08ffe3fb41fc 0xb7fe01ffcfff81f9 0xdbff00ffe7ffc0fc

def z636 : W := mkw 0x0000000000000000 0x0000000000000000 0xc80180007000701e 0x6400c0003800380f

def z637 : W := mkw 0x31c63777c76fc7d8 0x98e31bbbe3b7e3ec 0xbe867e7fce7fcf99 0x5f433f3fe73fe7cc

def z638 : W := mkw 0x8fedd97061f23b54 0x47f6ecb830f91daa 0xeff9f1f071e07fff 0xf7fcf8f838f03fff

def z639 : W := mkw 0x4c3bfead7e9c50aa 0x261dff56bf4e2855 0xff79ff8c7f9c71ff 0xffbcffc63fce38ff

def z640 : W := mkw 0x0400117060200354 0x020008b8301001aa 0x0000007000000000 0x0000003800000000

def z641 : W := mkw 0x20001235c62cc398 0x1000091ae31661cc 0xbe000e7fce1c4199 0x5f00073fe70e20cc

def z642 : W := mkw 0x20023635c62dc798 0x10011b1ae316e3cc 0x8a007e004e7fcf99 0x45003f00273fe7cc

def z643 : W := mkw 0x4da3fd617c000000 0x26d1feb0be000000 0x2d81fff07e000000 0x16c0fff83f000000

def z644 : W := mkw 0x200a3635c7ffc7f8 0x90051b1ae3ffe3fc 0xbe867e7fcfffcff9 0xdf433f3fe7ffe7fc

def z645 : W := mkw 0x0580117061600354 0x02c008b830b001aa 0xe78001f071e001ff 0xf3c000f838f000ff

def z646 : W := mkw 0x00080004009400a0 0x00040002004a0050 0x02000000019c01e1 0x8100000000ce00f0

def z647 : W := mkw 0x7df7fdfbfc218710 0x3efbfefdfe10c388 0x3dfffffffe638e00 0x1effffffff31c700

def z648 : W := mkw 0x0002343144200310 0x00011a18a2100188 0xbe867e7fce604f99 0x5f433f3fe73027cc

def z649 : W := mkw 0x2000001482248398 0x1000000a411241cc 0x8000000000000199 0x40000000000000cc

def z650 : W := mkw 0x0400102060000214 0x020008103000010a 0xc00000007000001e 0x600000003800000f

def z651 : W := mkw 0x0002363040294710 0x00011b182014a388 0xbe867e70407fcf99 0x5f433f38203fe7cc

def z652 : W := mkw 0x5df5c9ca38000000 0x2efae4e51c000000 0x35ff81ffb0000000 0x1affc0ffd8000000

def z653 : W := mkw 0x0002342144000000 0x00011a10a2000000 0x08007e004e000000 0x04003f0027000000

def z654 : W := mkw 0x0781414021402844 0x03c0a0a010a01422 0x6b81f18031e07e66 0xb5c0f8c018f03f33

def z655 : W := mkw 0x5ff7fdfb7d602b54 0x2ffbfefdbeb015aa 0x3dfffffffe600e00 0x1effffffff300700

def z656 : W := mkw 0x0781517061602b54 0x03c0a8b830b015aa 0xc50181f0718031ff 0xe280c0f838c018ff

def z657 : W := mkw 0x0581516060000000 0x02c0a8b030000000 0x0080707000000000 0x0040383800000000

def z658 : W := mkw 0x31febfffdfffd7fa 0x98ff5fffefffebfd 0xffffffffffffffff 0xffffffffffffffff

def z659 : W := mkw 0x5df7edca38000000 0x2efbf6e51c000000 0x39ffff8030000000 0x1cffffc018000000

def z660 : W := mkw 0x0621da207a087a1e 0x0310ed103d043d0f 0xc801fe007e007e1e 0x6400ff003f003f0f

def z661 : W := mkw 0x0000020000084000 0x0000010000042000 0x3a000e00001c4000 0x1d000700000e2000

def z662 : W := mkw 0x2603762166096e1c 0x1301bb10b304b70e 0xc801fe007e007e1e 0x6400ff003f003f0f

def z663 : W := mkw 0x00388a881a98502a 0x001c45440d4c2815 0xc9798f807f80707e 0xe4bcc7c03fc0383f

def z664 : W := mkw 0x8a21c80000003800 0x4510e40000001c00 0x0001800000003000 0x0000c00000001800

def z665 : W := mkw 0x8789537061fb7f54 0x43c4a9b830fdbfaa 0xef81f1f071ffffff 0xf7c0f8f838ffffff

def z666 : W := mkw 0x03a9ca0001d87800 0x01d4e50000ec3c00 0x3bf9fe0001fc7e00 0x1dfcff0000fe3f00

def z667 : W := mkw 0x00288a0000985000 0x00144500004c2800 0x10780e00001c0000 0x083c0700000e0000

def z668 : W := mkw 0x11dc01da81f28160 0x88ee00ed40f940b0 0x01fe01f381e38060 0x80ff00f9c0f1c030

def z669 : W := mkw 0x8be7ee00014b7c00 0x45f3f70000a5be00 0x0887fe000063fe00 0x0443ff000031ff00

def z670 : W := mkw 0x0038888c189410a2 0x001c44460c4a0851 0x7779818c319c31e7 0xbbbcc0c618ce18f3

def z671 : W := mkw 0x440010217c000000 0x22000810be000000 0x000000007e000000 0x000000003f000000

def z672 : W := mkw 0x31dc03de83ffc7f8 0x98ee01ef41ffe3fc 0xb7fe01ff81ffcff9 0xdbff00ffc0ffe7fc

def z673 : W := mkw 0x7df7ffeffe0dc488 0x3efbfff7ff06e244 0x3dfffffffe1f8000 0x1effffffff0fc000

def z674 : W := mkw 0x0581517060200354 0x02c0a8b8301001aa 0xed81f1f0700001ff 0xf6c0f8f8380000ff

def z675 : W := mkw 0x25837775e62dc798 0x12c1bbbaf316e3cc 0xbf87fffffe7fcf99 0x5fc3ffffff3fe7cc

def z676 : W := mkw 0x8befee0403df7caa 0x45f7f70201efbe55 0xfbfffe0001ffffff 0xfdffff0000ffffff

def z677 : W := mkw 0x07815174e164abd4 0x03c0a8ba70b255ea 0xff87f1fff1ffffff 0xffc3f8fff8ffffff

def z678 : W := mkw 0xaa23fe35c62dff98 0x5511ff1ae316ffcc 0xbe87fe7fce7fff99 0x5f43ff3fe73fffcc

def z679 : W := mkw 0x0781517061602b54 0x03c0a8b830b015aa 0xc48071f070600fff 0xe24038f8383007ff

def z680 : W := mkw 0x7ff7ffffff6defdc 0x3ffbffffffb6f7ee 0xffffffffffffffff 0xffffffffffffffff

def z681 : W := mkw 0x31d637ffc62dc798 0x18eb1bffe316e3cc 0xbffe7fffce7fcf99 0x5fff3fffe73fe7cc

def z682 : W := mkw 0x11fc89ca19d21062 0x88fe44e50ce90831 0x4179818031803066 0xa0bcc0c018c01833

def z683 : W := mkw 0x20023625460d4698 0x10011b12a306a34c 0xbe007e0c4e1c4f99 0x5f003f06270e27cc

def z684 : W := mkw 0xdffffffb7dfb7f54 0x6ffffffdbefdbfaa 0xffffffffffffffff 0xffffffffffffffff

def z685 : W := mkw 0x20023635c62dc798 0x10011b1ae316e3cc 0x8c007e7fce004f99 0x46003f3fe70027cc

def z686 : W := mkw 0xa20a3635c7ffff98 0x51051b1ae3ffffcc 0xbe867e7fcfffff99 0x5f433f3fe7ffffcc

def z687 : W := mkw 0x8fefff7061fb7f54 0x47f7ffb830fdbfaa 0x3bfffe7001fffe00 0x1dffff3800ffff00

def z688 : W := mkw 0x01c4000001420000 0x00e2000000a10000 0x0086000000638000 0x004300000031c000

def z689 : W := mkw 0x5dfffdeb7c901022 0x2efffef5be480811 0x7dffffffff803066 0xbeffffffffc01833

def z690 : W := mkw 0x0180015001600140 0x00c000a800b000a0 0xef8181f071e071ff 0xf7c0c0f838f038ff

def z691 : W := mkw 0x00288a04029c5088 0x00144502014e2844 0xbf798e0c4f9c7199 0x5fbcc70627ce38cc

def z692 : W := mkw 0x00000204020c4088 0x0000010201062044 0x10000e0c0e1c0000 0x08000706070e0000

def z693 : W := mkw 0x0018008c1a9400aa 0x000c00460d4a0055 0xf778018c7f9c01ff 0xfbbc00c63fce00ff

def z694 : W := mkw 0x0781415021602b54 0x03c0a0a810b015aa 0xc301818031e07fff 0xe180c0c018f03fff

def z695 : W := mkw 0x11c4015281628140 0x88e200a940b140a0 0x278601f381e381e1 0x93c300f9c0f1c0f0

def z696 : W := mkw 0x201a36bdc6bdc7b8 0x100d1b5ee35ee3dc 0xbffe7fffcfffcff9 0xdfff3fffe7ffe7fc

def z697 : W := mkw 0x5df5c9ca38000000 0x2efae4e51c000000 0x3d798f8c7e000000 0x1ebcc7c63f000000

def z698 : W := mkw 0x17dd41ca21d22864 0x8beea0e510e91432 0x4179818031803066 0xa0bcc0c018c01833

def z699 : W := mkw 0x8bfdca8c1bde78aa 0x45fee5460def3c55 0xff798f8c7f9c71ff 0xffbcc7c63fce38ff

def z700 : W := mkw 0x0783777061696f54 0x03c1bbb830b4b7aa 0xff87fff071ffffff 0xffc3fff838ffffff

def z701 : W := mkw 0x27815175e764abdc 0x13c0a8baf3b255ee 0xef81f1ffffe07fff 0xf7c0f8fffff03fff

def z702 : W := mkw 0x579151fb7d602b54 0x2bc8a8fdbeb015aa 0xef81f1ffffe07fff 0xf7c0f8fffff03fff

def z703 : W := mkw 0x0180000001400000 0x00c0000000a00000 0x2380000001e00000 0x11c0000000f00000

def z704 : W := mkw 0x0038888818901022 0x001c44440c480811 0x0078000000000000 0x003c000000000000

def z705 : W := mkw 0x26037635e62def9c 0x1301bb1af316f7ce 0xfe87fe7ffe7fff9f 0x7f43ff3fff3fffcf

def z706 : W := mkw 0x203abead5e9d56ba 0x101d5f56af4eab5d 0xff79ff8c7f9c7fff 0xffbcffc63fce3fff

def z707 : W := mkw 0x5df7fdeb7c000000 0x2efbfef5be000000 0x11ffffffbe000000 0x08ffffffdf000000

def z708 : W := mkw 0x0781516061402a54 0x03c0a8b030a0152a 0xef01f18071807fff 0xf780f8c038c03fff

def z709 : W := mkw 0x09f7fca95c000000 0x04fbfe54ae000000 0x3dfffffffe000000 0x1effffffff000000

def z710 : W := mkw 0xafc77571e563af54 0x57e3bab8f2b1d7aa 0x0086707380638e00 0x00433839c031c700

def z711 : W := mkw 0x11dc01de80b681a0 0x88ee00ef405b40d0 0x37fe01ff807f8181 0x1bff00ffc03fc0c0

def z712 : W := mkw 0x4de7fc217c000000 0x26f3fe10be000000 0x3dfffe7ffe000000 0x1effff3fff000000

def z713 : W := mkw 0x5df7fdeb7c000000 0x2efbfef5be000000 0x14fe7ffffe000000 0x0a7f3fffff000000

def z714 : W := mkw 0x59f6adcb1c000000 0x2cfb56e58e000000 0x3dff8ffffe000000 0x1effc7ffff000000

def z715 : W := mkw 0x20023635c62dc798 0x10011b1ae316e3cc 0xbf87fe7fcfffff99 0x5fc3ff3fe7ffffcc

def z716 : W := mkw 0x201010bdde248398 0x1008085eef1241cc 0x840001fffe000199 0x420000ffff0000cc

def z717 : W := mkw 0xdff7fdeb7d432c00 0x6ffbfef5bea19600 0x3fffffffffe3fe00 0x1ffffffffff1ff00

def z718 : W := mkw 0x701010bfde248398 0x3808085fef1241cc 0x8400007fce000199 0x4200003fe70000cc

def z719 : W := mkw 0x00388a8c1a9c50aa 0x001c45460d4e2855 0xffff8f8c7ffff1ff 0xffffc7c63ffff8ff

def z720 : W := mkw 0x11dc01de81f681e0 0x88ee00ef40fb40f0 0x11fe01ff81ff8060 0x88ff00ffc0ffc030

def z721 : W := mkw 0x20023635c62dc798 0x10011b1ae316e3cc 0xfe867e7fcfffffff 0xff433f3fe7ffffff

def z722 : W := mkw 0x55f499eb7c000000 0x2afa4cf5be000000 0x3dff8ffffe000000 0x1effc7ffff000000

def z723 : W := mkw 0x13dc01de81f6abf4 0x89ee00ef40fb55fa 0xffff81fff1ffffff 0xffffc0fff8ffffff

def z724 : W := mkw 0x8befee0001db7c00 0x45f7f70000edbe00 0x12fe7e0001fffe00 0x097f3f0000ffff00

def z725 : W := mkw 0x165d50aee096aab4 0x8b2ea857704b555a 0xd87ff00ff01ffe1e 0x6c3ff807f80fff0f

def z726 : W := mkw 0xd61813eb7ddb7c00 0x6b0c09f5beedbe00 0x060001fffffffe00 0x030000ffffffff00

def z727 : W := mkw 0x8befee0019db7c02 0x45f7f7000cedbe01 0x7bfffe0031fffe06 0x3dffff0018ffff03

def z728 : W := mkw 0x11e48b529b6ad14a 0x88f245a94db568a5 0xc8878e73fe63f01e 0x6443c739ff31f80f

def z729 : W := mkw 0x5dcf7767669c50aa 0x2ee7bbb3b34e2855 0xc2867073819c71ff 0xe1433839c0ce38ff

def z730 : W := mkw 0x27836745a74deccc 0x13c1b3a2d3a6f666 0x51078f8fbf9fb066 0xa883c7c7dfcfd833

def z731 : W := mkw 0x0180117041600350 0x00c008b820b001a8 0xef81f1f071e07fff 0xf7c0f8f838f03fff

def z732 : W := mkw 0x37c77573e563af54 0x9be3bab9f2b1d7aa 0x0086707380638e00 0x00433839c031c700

def z733 : W := mkw 0x0781415021602b54 0x03c0a0a810b015aa 0xeb81f18031e07fff 0xf5c0f8c018f03fff

def z734 : W := mkw 0x5df7fdeb7c000000 0x2efbfef5be000000 0x39fffe7f8e000000 0x1cffff3fc7000000

def z735 : W := mkw 0x0381503041602b10 0x01c0a81820b01588 0xef81f1f071e07fff 0xf7c0f8f838f03fff

def z736 : W := mkw 0x8befee001bdb7c0a 0x45f7f7000dedbe05 0xffffff807fffffff 0xffffffc03fffffff

def z737 : W := mkw 0x0866bc2144000000 0x04335e10a2000000 0x3cfe7e7fce000000 0x1e7f3f3fe7000000

def z738 : W := mkw 0x5ff7fdeb7d402844 0x2ffbfef5bea01422 0x7fffffffffe07e66 0xbffffffffff03f33

def z739 : W := mkw 0x11dc01da81f28160 0x88ee00ed40f940b0 0x33fe01f381ff8060 0x99ff00f9c0ffc030

def z740 : W := mkw 0x5df7fdeb7c000000 0x2efbfef5be000000 0x3cfe7e7fce000000 0x1e7f3f3fe7000000

def z741 : W := mkw 0x01cc000001d20000 0x00e6000000e90000 0x37fe007f81ff8000 0x1bff003fc0ffc000

def z742 : W := mkw 0x11dc01de81f681e0 0x88ee00ef40fb40f0 0x12fe007f81ff81e1 0x897f003fc0ffc0f0

def z743 : W := mkw 0x11dc01de83f681e8 0x88ee00ef41fb40f4 0xb7fe01ffcfff81f9 0xdbff00ffe7ffc0fc

def z744 : W := mkw 0x20023635c62dc7dc 0x10011b1ae316e3ee 0xfe867e7fce7fcfff 0xff433f3fe73fe7ff

def z745 : W := mkw 0xa208021483fffff8 0xd104010a41fffffc 0x8200000001fffff9 0xc100000000fffffc

def z746 : W := mkw 0x5ff7fdeb7d402844 0x2ffbfef5bea01422 0xffffffffff8071ff 0xffffffffffc038ff

def z747 : W := mkw 0x0be7ee0001496c00 0x05f3f70000a4b600 0x3bfffe0001fffe00 0x1dffff0000ffff00

def z748 : W := mkw 0xabedd835c7f6bb98 0x55f6ec1ae3fb5dcc 0x8579807fcf803199 0x42bcc03fe7c018cc

def z749 : W := mkw 0x5df7fdeb7c001002 0x2efbfef5be000801 0x7dfffffffe003006 0x3effffffff001803

def z750 : W := mkw 0x5df7fdeb7c010400 0x2efbfef5be008200 0x3dfffffffe638e00 0x1effffffff31c700

def z751 : W := mkw 0x5c77fcab7c000000 0x2e3bfe55be000000 0x3cfffe7ffe000000 0x1e7fff3fff000000

def z752 : W := mkw 0x11d401de816481c0 0x08ea00ef40b240e0 0x37fe01ff81ff81e1 0x9bff00ffc0ffc0f0

def z753 : W := mkw 0x9a33efde802dfde0 0xcd19f7ef4016fef0 0x0c01ffff80007fe1 0x8600ffffc0003ff0

def z754 : W := mkw 0x5df5d9eb7c000000 0x2efaecf5be000000 0x3d798ffffe000000 0x1ebcc7ffff000000

def z755 : W := mkw 0x01c6342144000000 0x00e31a10a2000000 0x3dfe7e7fce000000 0x1eff3f3fe7000000

def z756 : W := mkw 0x0008021482bcd1aa 0x0004010a415e68d5 0xc200000001fff1ff 0xe100000000fff8ff

def z757 : W := mkw 0x11dc01de81f681e0 0x88ee00ef40fb40f0 0x3fff81ff81fff1e1 0x9fffc0ffc0fff8f0

def z758 : W := mkw 0x11dc01de81f683f4 0x88ee00ef40fb41fa 0xf7fe01ff81ff81ff 0xfbff00ffc0ffc0ff

def z759 : W := mkw 0x01eeae0001db5400 0x00f7570000edaa00 0x3bfffe0001fffe00 0x1dffff0000ffff00

def z760 : W := mkw 0x5dd775eb64000000 0x2eebbaf5b2000000 0x3dfe7fffce000000 0x1eff3fffe7000000

def z761 : W := mkw 0x341011ffe62483fc 0x9a0808fff31241fe 0xc40001fffe0001ff 0xe20000ffff0000ff

def z762 : W := mkw 0xdffdc9ca39d23860 0xeffee4e51ce91c30 0x0179818031803060 0x80bcc0c018c01830

def z763 : W := mkw 0x141011fefa2483fe 0x8a0808ff7d1241ff 0xc40001fffe0001ff 0xe20000ffff0000ff

def z764 : W := mkw 0x27815171e560ab54 0x13c0a8b8f2b055aa 0xef81f1f3f1e07fff 0xf7c0f8f9f8f03fff

def z765 : W := mkw 0x5df7fdeb7c000000 0x2efbfef5be000000 0x0d79fffffe000000 0x06bcffffff000000

def z766 : W := mkw 0x2008021482bdd7ba 0x1004010a415eebdd 0x82000000007fcf99 0x41000000003fe7cc

def z767 : W := mkw 0x5781517365602b54 0x2bc0a8b9b2b015aa 0xef81f1f3f1e07fff 0xf7c0f8f9f8f03fff

def z768 : W := mkw 0x20023435c4258790 0x10011a1ae212c3c8 0x3e867e7fce7f8f81 0x1f433f3fe73fc7c0

def z769 : W := mkw 0x741011fffe2483dc 0x3a0808ffff1241ee 0xc40001fffe0001ff 0xe20000ffff0000ff

def z770 : W := mkw 0xae23fe2166097e1c 0x5711ff10b304bf0e 0xc801fe007e007e1e 0x6400ff003f003f0f

def z771 : W := mkw 0x20023635c62dc798 0x10011b1ae316e3cc 0xfe867ffffe7fcfff 0xff433fffff3fe7ff

def z772 : W := mkw 0x201010bdde2483ba 0x1008085eef1241dd 0x8400007fce000199 0x4200003fe70000cc

def z773 : W := mkw 0x13dd41de81f6abf4 0x89eea0ef40fb55fa 0xfffff1ff81ffffff 0xfffff8ffc0ffffff

def z774 : W := mkw 0x8befee0001db7c00 0x45f7f70000edbe00 0xbffffe0041ffff99 0x5fffff0020ffffcc

def z775 : W := mkw 0x0781516060002a14 0x03c0a8b03000150a 0xef81f1f071807fff 0xf7c0f8f838c03fff

def z776 : W := mkw 0x5df7fdeb7c000060 0xaefbfef5be000030 0x3dfffffffe000060 0x9effffffff000030

def z777 : W := mkw 0x886eae00009b5400 0x44375700004daa00 0x3bfffe0001fffe00 0x1dffff0000ffff00

def z778 : W := mkw 0x8c6ebf7060bb5754 0x46375fb8305dabaa 0xd47e0ff0701f81ff 0xea3f07f8380fc0ff

def z779 : W := mkw 0x11dc01ce809680a0 0x88ee00e7404b4050 0x10fe007f801f8000 0x087f003fc00fc000

def z780 : W := mkw 0x11dc01de81f681e0 0x88ee00ef40fb40f0 0xf7fe01ff81fff1ff 0xfbff00ffc0fff8ff

def z781 : W := mkw 0x7df5cbdeba2dc798 0x3efae5ef5d16e3cc 0x83798180307fcf99 0x41bcc0c0183fe7cc

def z782 : W := mkw 0x11d401ce80048080 0x08ea00e740024040 0x35fe01ff801f8000 0x1aff00ffc00fc000

def z783 : W := mkw 0x05b3fde97c000000 0x02d9fef4be000000 0x3dfffffffe000000 0x1effffffff000000

def z784 : W := mkw 0x5df7fdeb7c000022 0x2efbfef5be000011 0x7dfffffffe000066 0xbeffffffff000033

def z785 : W := mkw 0x987eae8e9a9fd4aa 0xcc3f57474d4fea55 0x107e0e0f8e1f8000 0x083f0707c70fc000

def z786 : W := mkw 0x31de37eb47db4678 0x98ef1bf5a3eda33c 0x89787f804f804e78 0xc4bc3fc027c0273c

def z787 : W := mkw 0x8befee0001db7c60 0xc5f7f70000edbe30 0x3bfffe0001fffe60 0x9dffff0000ffff30

def z788 : W := mkw 0x2823fe2146094618 0x1411ff10a304a30c 0x8801fe004e004e18 0x4400ff002700270c

def z789 : W := mkw 0x8a2bee0001db7c00 0x4515f70000edbe00 0x3b79fe0001fffe00 0x1dbcff0000ffff00

def z790 : W := mkw 0x0866ae0000094400 0x043357000004a200 0x3afe7e00007fce00 0x1d7f3f00003fe700

def z791 : W := mkw 0x20023635c62dc798 0x10011b1ae316e3cc 0xbf867fffcfffcff9 0xdfc33fffe7ffe7fc

def z792 : W := mkw 0x20023635c62dd79a 0x10011b1ae316ebcd 0xfe867e7fce7fff9f 0x7f433f3fe73fffcf

def z793 : W := mkw 0x0010009c80248180 0x0008004e401240c0 0x37fe01ff807f8181 0x1bff00ffc03fc0c0

def z794 : W := mkw 0x101011fec02483f0 0x880808ff601241f8 0x840001ffc00001f9 0xc20000ffe00000fc

def z795 : W := mkw 0x0de7fd6164000000 0x06f3feb0b2000000 0x3dfffffffe000000 0x1effffffff000000

def z796 : W := mkw 0x07815170e162ab54 0x83c0a8b870b155aa 0xef81f1f071e3ffff 0xf7c0f8f838f1ffff

def z797 : W := mkw 0x5df7fdeb7d420000 0x2efbfef5bea10000 0x3dfffffffe638000 0x1effffffff31c000

def z798 : W := mkw 0x8a6fee00009b7c00 0x4537f700004dbe00 0x3afffe00007ffe00 0x1d7fff00003fff00

def z799 : W := mkw 0x201010bdc62483b8 0x1008085ee31241dc 0x840001ffce0001f9 0xc20000ffe70000fc

def z800 : W := mkw 0x787eae8f9e9dd4aa 0x3c3f5747cf4eea55 0x107e0e0f8e1f8000 0x083f0707c70fc000

def z801 : W := mkw 0x01cc001081f28100 0x00e6000840f94080 0x33fe007381ff8000 0x19ff0039c0ffc000

def z802 : W := mkw 0x4c33fca97c000000 0x2619fe54be000000 0x3dfffffffe000000 0x1effffffff000000

def z803 : W := mkw 0x0400117060200354 0x020008b8301001aa 0xef81f1f071e07fff 0xf7c0f8f838f03fff

def z804 : W := mkw 0x13dd41de81f6a9e0 0x89eea0ef40fb54f0 0x37fe71ff81ff8fe1 0x9bff38ffc0ffc7f0

def z805 : W := mkw 0x0601503060202b14 0x0300a8183010158a 0xef81f1f071e07fff 0xf7c0f8f838f03fff

def z806 : W := mkw 0x09efee0000995400 0x04f7f700004caa00 0x3bfffe0001fffe00 0x1dffff0000ffff00

def z807 : W := mkw 0x20023635c62dc798 0x10011b1ae316e3cc 0x98867e7fce7fce18 0x4c433f3fe73fe70c

def z808 : W := mkw 0x11dc01ce81d680a0 0x88ee00e740eb4050 0x37fe01ff81ff8000 0x1bff00ffc0ffc000

def z809 : W := mkw 0x5a76ac9b1d602b54 0x2d3b564d8eb015aa 0xd27e0e0f8fe07fff 0xe93f0707c7f03fff

def z810 : W := mkw 0x07c5517061602b54 0x03e2a8b830b015aa 0xfffff1f071e07fff 0xfffff8f838f03fff

def z811 : W := mkw 0x8208021483fffdea 0xc104010a41fffef5 0xc200000001ffffff 0xe100000000ffffff

def z812 : W := mkw 0x8fefef4021db7c44 0x47f7f7a010edbe22 0xffffff8071ffffff 0xffffffc038ffffff

def z813 : W := mkw 0x5df7edcb3c000000 0x2efbf6e59e000000 0x35ff8fffbe000000 0x1affc7ffdf000000

def z814 : W := mkw 0x2208021483fdfffe 0x1104010a41feffff 0xc200000001ffffff 0xe100000000ffffff

def z815 : W := mkw 0x001234a944000000 0x00091a54a2000000 0x3dfe7fffce000000 0x1eff3fffe7000000

def z816 : W := mkw 0x17dd41dea1f6a9e4 0x8beea0ef50fb54f2 0xffff81fff1fff1ff 0xffffc0fff8fff8ff

def z817 : W := mkw 0x105c01de80b681e0 0x882e00ef405b40f0 0x377e01ff819f81e1 0x9bbf00ffc0cfc0f0

def z818 : W := mkw 0x8be7ee00014b6c00 0x45f3f70000a5b600 0x3bfffe00007fce00 0x1dffff00003fe700

def z819 : W := mkw 0x2008021482bfc7b8 0x9004010a415fe3dc 0x82000000007fcf99 0x41000000003fe7cc

def z820 : W := mkw 0x11dc01de81f681e0 0x88ee00ef40fb40f0 0x157e01ff819f81e1 0x8abf00ffc0cfc0f0

def z821 : W := mkw 0x5ff7fdeb7d402800 0x2ffbfef5bea01400 0x3dffffffff803000 0x1effffffffc01800

def z822 : W := mkw 0x11dc01de81f681e0 0x88ee00ef40fb40f0 0x3fff81fff1ff81e1 0x9fffc0fff8ffc0f0

def z823 : W := mkw 0x8befee0001db7c00 0x45f7f70000edbe00 0x3ffffe7f81fffe00 0x1fffff3fc0ffff00

def z824 : W := mkw 0xce23fe217e097c0a 0x6711ff10bf04be05 0xc801fe007e007e1e 0x6400ff003f003f0f

def z825 : W := mkw 0xdff7fdeb7c003800 0x6ffbfef5be001c00 0x3dfffffffe003000 0x1effffffff001800

def z826 : W := mkw 0x8befee0019db7c00 0x45f7f7000cedbe00 0x3bfffe007ffffe00 0x1dffff003fffff00

def z827 : W := mkw 0x8a2bee0000997c00 0x4515f700004cbe00 0x3bfffe0001fffe00 0x1dffff0000ffff00

def z828 : W := mkw 0x5ff7fdeb7d402800 0x2ffbfef5bea01400 0xffffffffffe07fff 0xfffffffffff03fff

def z829 : W := mkw 0x5df7fdeb7c000000 0x2efbfef5be000000 0x157f8ffffe000000 0x0abfc7ffff000000

def z830 : W := mkw 0x83ce260001db7c00 0x41e7130000edbe00 0x3bfe7e0001fffe00 0x1dff3f0000ffff00

def z831 : W := mkw 0x141011fee02483f4 0x8a0808ff701241fa 0x040001ff800001e1 0x820000ffc00000f0

def z832 : W := mkw 0x11cc015681f681c0 0x88e600ab40fb40e0 0x37fe007f81ff8181 0x1bff003fc0ffc0c0

def z833 : W := mkw 0x93dc01de81f6b9e0 0xc9ee00ef40fb5cf0 0x37fe01ff81ffb1e1 0x9bff00ffc0ffd8f0

def z834 : W := mkw 0x886eae00009b5400 0x44375700004daa00 0x10fe7e00007f8e00 0x087f3f00003fc700

def z835 : W := mkw 0x10388a8e9a9cd0aa 0x881c45474d4e6855 0xff798f8fff9c71ff 0xffbcc7c7ffce38ff

def z836 : W := mkw 0x11dc01de81f691e2 0x88ee00ef40fb48f1 0x77fe01ff81ffb1e7 0xbbff00ffc0ffd8f3

def z837 : W := mkw 0x105c008e809680a0 0x882e0047404b4050 0x34fe007f801f8000 0x1a7f003fc00fc000

def z838 : W := mkw 0x307eae8f9e9fd4aa 0x983f5747cf4fea55 0x107e0e0f8e1f8000 0x083f0707c70fc000

def z839 : W := mkw 0x2008021482bdd798 0x1004010a415eebcc 0x8200000001ffff99 0x4100000000ffffcc

def z840 : W := mkw 0x8befee001bdb7c0a 0x45f7f7000dedbe05 0x3bfffe000ffffe00 0x1dffff0007ffff00

def z841 : W := mkw 0x301011ffc42483f0 0x980808ffe21241f8 0x040001ff800001e1 0x820000ffc00000f0

def z842 : W := mkw 0x0018028c029c40a8 0x000c0146014e2054 0xff798f8c7f9c71ff 0xffbcc7c63fce38ff

def z843 : W := mkw 0x20388a8c9a9dd4aa 0x101c45464d4eea55 0xff798f8c7f9ff1ff 0xffbcc7c63fcff8ff

def z844 : W := mkw 0x5876adcb1c000000 0x2c3b56e58e000000 0x147e0fff8e000000 0x0a3f07ffc7000000

def z845 : W := mkw 0x01cc001481f681e0 0x80e6000a40fb40f0 0x37fe007f81ff81e1 0x9bff003fc0ffc0f0

def z846 : W := mkw 0x5df6bdeb7c000000 0x2efb5ef5be000000 0x35fe0ffffe000000 0x1aff07ffff000000

def z847 : W := mkw 0x00388a8c1a9c50aa 0x001c45460d4e2855 0xcb798f807f9c71ff 0xe5bcc7c03fce38ff

def z848 : W := mkw 0x11dc01de81f681e0 0x88ee00ef40fb40f0 0xf7fe01fff1ff81ff 0xfbff00fff8ffc0ff

def z849 : W := mkw 0xaa23fe2144097e10 0x5511ff10a204bf08 0x0801fe0000007e00 0x0400ff0000003f00

def z850 : W := mkw 0x0781516061402800 0x03c0a8b030a01400 0xef81f1f071e07fff 0xf7c0f8f838f03fff

def z851 : W := mkw 0x2008021483ffc5e8 0x9004010a41ffe2f4 0x0200000001ff81e1 0x8100000000ffc0f0

def z852 : W := mkw 0x883aae8c1a9d54aa 0x441d57460d4eaa55 0x10780e0c0e1c0000 0x083c0706070e0000

def z853 : W := mkw 0xcc23fe217c095400 0x6611ff10be04aa00 0x0801fe007e000000 0x0400ff003f000000

def z854 : W := mkw 0x11d401ca00000000 0x08ea00e500000000 0x37fe01ff807f8000 0x1bff00ffc03fc000

def z855 : W := mkw 0x0018009c80b481a0 0x000c004e405a40d0 0x36fe007f807f8181 0x1b7f003fc03fc0c0

def z856 : W := mkw 0x15d775eb64000000 0x0aebbaf5b2000000 0x3dfffffffe000000 0x1effffffff000000

def z857 : W := mkw 0x8a23fe2144097c00 0x4511ff10a204be00 0x0801fe004e007e00 0x0400ff0027003f00

def z858 : W := mkw 0x13dd41de81f6a9e0 0x89eea0ef40fb54f0 0xfffff1fff1ffffff 0xfffff8fff8ffffff

def z859 : W := mkw 0x5df7fdeb7c000000 0x2efbfef5be000000 0x7dffffffff803066 0xbeffffffffc01833

def z860 : W := mkw 0xdff7fdeb7c012c00 0x6ffbfef5be009600 0x3dfffffffe000e00 0x1effffffff000700

def z861 : W := mkw 0x8bcf660001db7c00 0x45e7b30000edbe00 0x33fe700001fffe00 0x19ff380000ffff00

def z862 : W := mkw 0x01cc000001d20000 0x00e6000000e90000 0x3bfe700001ffce00 0x1dff380000ffe700

def z863 : W := mkw 0x0781517165602b54 0x03c0a8b8b2b015aa 0xef81f1ffffe07fff 0xf7c0f8fffff03fff

def z864 : W := mkw 0x8fc5517061622b54 0x47e2a8b830b115aa 0xef81f1f071e07fff 0xf7c0f8f838f03fff

def z865 : W := mkw 0x8bedc80001d23800 0x45f6e40000e91c00 0x3bfff00001fffe00 0x1dfff80000ffff00

def z866 : W := mkw 0x00388a8818985000 0x001c45440c4c2800 0xff798f8c7f9c71ff 0xffbcc7c63fce38ff

def z867 : W := mkw 0x89eeae0001db5400 0x44f7570000edaa00 0x3bfe7e0001ffce00 0x1dff3f0000ffe700

def z868 : W := mkw 0x004e2600009b4400 0x00271300004da200 0x3afe7e00007fce00 0x1d7f3f00003fe700

def z869 : W := mkw 0x105c01de81f681e0 0x882e00ef40fb40f0 0x167e01ff81ff81e1 0x8b3f00ffc0ffc0f0

def z870 : W := mkw 0x07b9dbfc7bfc7bfe 0x03dcedfe3dfe3dff 0x10f87e7c0e7c0e00 0x087c3f3e073e0700

def z871 : W := mkw 0x11dd41de81f681e0 0x88eea0ef40fb40f0 0x3ffff1ff81ff81e1 0x9ffff8ffc0ffc0f0

def z872 : W := mkw 0x4c2bfc35fdf681e0 0xa615fe1afefb40f0 0x0a01fe007fff81e1 0x8500ff003fffc0f0

def z873 : W := mkw 0x8a6fee0001db7c00 0x4537f70000edbe00 0x1a7ffe0001fffe00 0x0d3fff0000ffff00

def z874 : W := mkw 0x5df7fdeb7c000000 0x2efbfef5be000000 0x3ffffffffe7f8000 0x1fffffffff3fc000

def z875 : W := mkw 0x11dc01ce01d600a0 0x08ee00e700eb0050 0x37fe01ff81ff81e1 0x9bff00ffc0ffc0f0

def z876 : W := mkw 0x2208021483ffeffc 0x9104010a41fff7fe 0xc200000001ffffff 0xe100000000ffffff

def z877 : W := mkw 0x2008021482bcd3ba 0x1004010a415e69dd 0xc2000000019c71ff 0xe100000000ce38ff

def z878 : W := mkw 0x83a9ca0001db7c00 0x41d4e50000edbe00 0x3bf9fe0001fffe00 0x1dfcff0000ffff00

def z879 : W := mkw 0x2008021482bdc7b8 0x1004010a415ee3dc 0x8200000001ffcff9 0xc100000000ffe7fc

def z880 : W := mkw 0x5df7fdeb7c000000 0x2efbfef5be000000 0xfdfffffffe0001ff 0xfeffffffff0000ff

def z881 : W := mkw 0x11dc01de80b481a0 0x08ee00ef405a40d0 0x37fe01ff81ff81e1 0x9bff00ffc0ffc0f0

def z882 : W := mkw 0x5de7fd6364000000 0x2ef3feb1b2000000 0x3dfffe7fce000000 0x1effff3fe7000000

def z883 : W := mkw 0x11dc01de83f681ea 0x88ee00ef41fb40f5 0xf7fe01ff81ff81ff 0xfbff00ffc0ffc0ff

def z884 : W := mkw 0x11cc014201d20000 0x08e600a100e90000 0x33fe007381ff8000 0x19ff0039c0ffc000

def z885 : W := mkw 0x0601517061602b54 0x0300a8b830b015aa 0xce01f1f071e07fff 0xe700f8f838f03fff

def z886 : W := mkw 0x5ffdc9ca39d22864 0xaffee4e51ce91432 0x4179818031803066 0xa0bcc0c018c01833

def z887 : W := mkw 0x20023635c62dc798 0x10011b1ae316e3cc 0x3c867e7fce7f8e00 0x1e433f3fe73fc700

def z888 : W := mkw 0x8befec0001d33c00 0x45f7f60000e99e00 0x33fff00001ffbe00 0x19fff80000ffdf00

def z889 : W := mkw 0x8befee0001db7c00 0x45f7f70000edbe00 0x39fffe00007f8e00 0x1cffff00003fc700

def z890 : W := mkw 0x203abcb9dcb19732 0x101d5e5cee58cb99 0x41fff1f3b1e3be66 0xa0fff8f9d8f1df33

def z891 : W := mkw 0x59f7fcab5c000000 0x2cfbfe55ae000000 0x3dfffe7fce000000 0x1effff3fe7000000

def z892 : W := mkw 0x301011ffc6248398 0x180808ffe31241cc 0x840001ffce000199 0x420000ffe70000cc

def z893 : W := mkw 0x0000000000000000 0x0000000000000000 0xef81f18071e07fff 0xf7c0f8c038f03fff

def z894 : W := mkw 0x17dd41dea1f6abf4 0x8beea0ef50fb55fa 0xf7ff81ffb1ffffff 0xfbffc0ffd8ffffff

def z895 : W := mkw 0x19f7edca18000000 0x0cfbf6e50c000000 0x3dfffffffe000000 0x1effffffff000000

def z896 : W := mkw 0x0022ae0000094400 0x001157000004a200 0x3bfffe00007fce00 0x1dffff00003fe700

def z897 : W := mkw 0x5df7fdeb7c000000 0x2efbfef5be000000 0xfdfffffffe00701e 0x7effffffff00380f

def z898 : W := mkw 0x20023635c62dc798 0x10011b1ae316e3cc 0xbf87fffffe7fcf99 0x5fc3ffffff3fe7cc

def z899 : W := mkw 0x741011fffe2483ba 0x3a0808ffff1241dd 0xc40001fffe0001ff 0xe20000ffff0000ff

def z900 : W := mkw 0x5c77fdeb7c000000 0x2e3bfef5be000000 0x1c7ffffffe000000 0x0e3fffffff000000

def z901 : W := mkw 0x8bcf640001d32c00 0x45e7b20000e99600 0x3bfff00001fffe00 0x1dfff80000ffff00

def z902 : W := mkw 0x01ce240001d30400 0x00e7120000e98200 0x33fe700001ff8e00 0x19ff380000ffc700

def z903 : W := mkw 0xcfefee0039db7c00 0x67f7f7001cedbe00 0x3bfffe0031fffe00 0x1dffff0018ffff00

def z904 : W := mkw 0x105c01ce809680a0 0x882e00e7404b4050 0x147e01ff801f8000 0x0a3f00ffc00fc000

def z905 : W := mkw 0x8befee0001db7c00 0x45f7f70000edbe00 0x3fffff8001ffffe1 0x9fffffc000fffff0

def z906 : W := mkw 0x2022be215e094618 0x10115f10af04a30c 0x8801fe007e004e18 0x4400ff003f00270c

def z907 : W := mkw 0x11dc01de99f681e0 0x88ee00ef4cfb40f0 0x37fe01ffffff81e1 0x9bff00ffffffc0f0

def z908 : W := mkw 0x002aae0000995400 0x00155700004caa00 0x3afe7e00007fce00 0x1d7f3f00003fe700

def z909 : W := mkw 0x6e23fe217e096e1c 0x3711ff10bf04b70e 0xc801fe007e007e1e 0x6400ff003f003f0f

def z910 : W := mkw 0x5c76bdeb7c000000 0x2e3b5ef5be000000 0x3cfe7ffffe000000 0x1e7f3fffff000000

def z911 : W := mkw 0x004c001480b68180 0x0026000a405b40c0 0x36fe007f807f8181 0x1b7f003fc03fc0c0

def z912 : W := mkw 0x11dc01de81f681e0 0x88ee00ef40fb40f0 0x03fe01f381ff81e1 0x81ff00f9c0ffc0f0

def z913 : W := mkw 0x543099eb7c000000 0x2a184cf5be000000 0x14780ffffe000000 0x0a3c07ffff000000

def z914 : W := mkw 0x8befef4001db7c40 0x45f7f7a000edbe20 0x3bffff8001fffe60 0x9dffffc000ffff30

def z915 : W := mkw 0x5c76bdeb7c000000 0x2e3b5ef5be000000 0x107e0e7f8e000000 0x083f073fc7000000

def z916 : W := mkw 0x8befee0001db7c00 0x45f7f70000edbe00 0xfbfffe0071fffe1e 0x7dffff0038ffff0f

def z917 : W := mkw 0x0032bca95c000000 0x00195e54ae000000 0x3cfe7e7fce000000 0x1e7f3f3fe7000000

def z918 : W := mkw 0x59f6bdeb5c000000 0x2cfb5ef5ae000000 0x3dfe7fffce000000 0x1eff3fffe7000000

def z919 : W := mkw 0x003098a95c000000 0x00184c54ae000000 0x3d798ffffe000000 0x1ebcc7ffff000000

def z920 : W := mkw 0x8fefef4021db7c44 0x47f7f7a010edbe22 0x3bfffe0001fffe00 0x1dffff0000ffff00

def z921 : W := mkw 0x8bedca0001db7c00 0x45f6e50000edbe00 0x2bf9f00001fffe00 0x15fcf80000ffff00

def z922 : W := mkw 0x8befef4001db7c00 0x45f7f7a000edbe00 0x3ffffff001fffe00 0x1ffffff800ffff00

def z923 : W := mkw 0x0038888c189400a0 0x001c44460c4a0050 0xff798f8c7f9c71ff 0xffbcc7c63fce38ff

def z924 : W := mkw 0x0201400000002800 0x0100a00000001400 0xef01f18071807fff 0xf780f8c038c03fff

def z925 : W := mkw 0x00388a8c1a9c50aa 0x001c45460d4e2855 0xcd798f8c7f8071ff 0xe6bcc7c63fc038ff

def z926 : W := mkw 0x0038888c1a9410aa 0x001c44460d4a0855 0xfd798f8c7f8031ff 0xfebcc7c63fc018ff

def z927 : W := mkw 0x0008021483fec1e8 0x8004010a41ff60f4 0x8200000001ffc1f9 0xc100000000ffe0fc

def z928 : W := mkw 0x105c009e81f681e0 0x882e004f40fb40f0 0x36fe007f81ff81e1 0x9b7f003fc0ffc0f0

def z929 : W := mkw 0x8befee0001db7c00 0x45f7f70000edbe00 0xfbfffe0001ffffff 0xfdffff0000ffffff

def z930 : W := mkw 0x8befee0003db7c0a 0x45f7f70001edbe05 0xfbfffe0001fffe1e 0x7dffff0000ffff0f

def z931 : W := mkw 0x11dc01de81f681e0 0x88ee00ef40fb40f0 0x3ffe71ff81ffcfe1 0x9fff38ffc0ffe7f0

def z932 : W := mkw 0x5df7fdeb7d420040 0xaefbfef5bea10020 0x3dfffffffe000000 0x1effffffff000000

def z933 : W := mkw 0x8befee0001db7c00 0x45f7f70000edbe00 0x18fffe00007ffe00 0x0c7fff00003fff00

def z934 : W := mkw 0x80388a8c1a9f54aa 0x401c45460d4faa55 0xff798f8c7f9ff1ff 0xffbcc7c63fcff8ff

def z935 : W := mkw 0x31dc01de83f683f8 0x98ee00ef41fb41fc 0xb7fe01ff81ff81f9 0xdbff00ffc0ffc0fc

def z936 : W := mkw 0x105c009e80b681a0 0x882e004f405b40d0 0x10fe007f807f8000 0x087f003fc03fc000

def z937 : W := mkw 0x11dc01de9bf681ea 0x88ee00ef4dfb40f5 0x37fe01ff8fff81e1 0x9bff00ffc7ffc0f0

def z938 : W := mkw 0x11cc015281f28140 0x88e600a940f940a0 0x37fe01f381ff81e1 0x9bff00f9c0ffc0f0

def z939 : W := mkw 0x301011ffde2483fa 0x980808ffef1241fd 0xc40001fffe0001ff 0xe20000ffff0000ff

def z940 : W := mkw 0x00388a8c1a9c50aa 0x001c45460d4e2855 0xfff9ff8c7ffc7fff 0xfffcffc63ffe3fff

def z941 : W := mkw 0x0008021483fed1ea 0x8004010a41ff68f5 0x0200000001ff81e1 0x8100000000ffc0f0

def z942 : W := mkw 0x7fc77573e561af54 0x3fe3bab9f2b0d7aa 0x0086707380638e00 0x00433839c031c700

def z943 : W := mkw 0x8befee0001db7c44 0x45f7f70000edbe22 0x7bfffe0001fffe66 0xbdffff0000ffff33

def z944 : W := mkw 0x20023635c62dc798 0x10011b1ae316e3cc 0x3a867e7f8e7fce00 0x1d433f3fc73fe700

def z945 : W := mkw 0xa822be2146095618 0x54115f10a304ab0c 0x88007e004e004e18 0x44003f002700270c

def z946 : W := mkw 0x11dc01de81f681e0 0x88ee00ef40fb40f0 0x35fe01ff807f8000 0x1aff00ffc03fc000

def z947 : W := mkw 0x11f489ca18000000 0x08fa44e50c000000 0x35fe0fff8e000000 0x1aff07ffc7000000

def z948 : W := mkw 0x07c5517061622b54 0x03e2a8b830b115aa 0xef87f1f071e3ffff 0xf7c3f8f838f1ffff

def z949 : W := mkw 0x17815172e160ab54 0x8bc0a8b970b055aa 0xef81f1f3f1e07fff 0xf7c0f8f9f8f03fff

def z950 : W := mkw 0x11dc009e81f681a0 0x88ee004f40fb40d0 0x37fe007f81ff8181 0x1bff003fc0ffc0c0

def z951 : W := mkw 0x8befee0001db7c00 0x45f7f70000edbe00 0x3ffffe0c4ffffe00 0x1fffff0627ffff00

def z952 : W := mkw 0x5876bcab5c000000 0x2c3b5e55ae000000 0x10fe7e7f8e000000 0x087f3f3fc7000000

def z953 : W := mkw 0x0208021483fefbfe 0x8104010a41ff7dff 0xc200000001ffffff 0xe100000000ffffff

def z954 : W := mkw 0x0381401001602b54 0x01c0a00800b015aa 0xef81f18071e07fff 0xf7c0f8c038f03fff

def z955 : W := mkw 0x9befef4201db7c40 0xcdf7f7a100edbe20 0x3bfffe0001fffe00 0x1dffff0000ffff00

def z956 : W := mkw 0x105c01de80b681e0 0x882e00ef405b40f0 0x107e007f801f8000 0x083f003fc00fc000

def z957 : W := mkw 0x0781517061602b54 0x03c0a8b830b015aa 0xff87f1f071ffffff 0xffc3f8f838ffffff

def z958 : W := mkw 0xdff7fdeb7d422800 0x6ffbfef5bea11400 0x3dfffffffe000000 0x1effffffff000000

def z959 : W := mkw 0x5df7fdeb7c000214 0x2efbfef5be00010a 0xfdfffffffe00001e 0x7effffffff00000f

def z960 : W := mkw 0x0381415001602940 0x01c0a0a800b014a0 0xef81f1f071e07fff 0xf7c0f8f838f03fff

def z961 : W := mkw 0x1054009e80248180 0x082a004f401240c0 0x36fe007f807f8181 0x1b7f003fc03fc0c0

def z962 : W := mkw 0x11dc01de81f681e0 0x88ee00ef40fb40f0 0x36fe007f807f8181 0x1b7f003fc03fc0c0

def z963 : W := mkw 0x5df7fdeb7c000210 0x2efbfef5be000108 0xbdfffffffe004e18 0x5effffffff00270c

def z964 : W := mkw 0x11dc01da01f20140 0x08ee00ed00f900a0 0x37fe01ff81ff81e1 0x9bff00ffc0ffc0f0

def z965 : W := mkw 0x6822be215e094618 0x34115f10af04a30c 0x88007e004e004e18 0x44003f002700270c

def z966 : W := mkw 0x15f5d9ea78000000 0x0afaecf53c000000 0x3dfffffffe000000 0x1effffffff000000

def z967 : W := mkw 0x01dc009c81f681a0 0x00ee004e40fb40d0 0x37fe01ff81ff81e1 0x9bff00ffc0ffc0f0

def z968 : W := mkw 0x5ff7fdeb7d402800 0x2ffbfef5bea01400 0x3dfffffffe600e00 0x1effffffff300700

def z969 : W := mkw 0x11d401ca00000000 0x08ea00e500000000 0x3dfe0fffce000000 0x1eff07ffe7000000

def z970 : W := mkw 0xd87eae8f1e9f54aa 0x6c3f57478f4faa55 0x107e0e0f8e1f8000 0x083f0707c70fc000

def z971 : W := mkw 0x11dc01de81f681e0 0x88ee00ef40fb40f0 0x77ff81ffb1ffb1e7 0xbbffc0ffd8ffd8f3

def z972 : W := mkw 0x000a260000994400 0x00051300004ca200 0x3bfe7e0001ffce00 0x1dff3f0000ffe700

def z973 : W := mkw 0x0781502061402a14 0x03c0a81030a0150a 0xef81f18071e07fff 0xf7c0f8c038f03fff

def z974 : W := mkw 0x20023631c429c710 0x10011b18e214e388 0x3e867e7fce7fce00 0x1f433f3fe73fe700

def z975 : W := mkw 0x20023635c62dc798 0x10011b1ae316e3cc 0x94867e7fce7f8f99 0x4a433f3fe73fc7cc

def z976 : W := mkw 0xa87eae8d9e9fd4aa 0x543f5746cf4fea55 0x107e0e0f8e1f8000 0x083f0707c70fc000

def z977 : W := mkw 0x8bd7648c1b472caa 0x45ebb2460da39655 0xc486718c7e638fff 0xe24338c63f31c7ff

def z978 : W := mkw 0x20022615862dc588 0x1001130ac316e2c4 0x3e867e7f8e7fcf81 0x1f433f3fc73fe7c0

def z979 : W := mkw 0x03abee0001d97c00 0x01d5f70000ecbe00 0x3bfffe0001fffe00 0x1dffff0000ffff00

def z980 : W := mkw 0x11d625cb04000000 0x08eb12e582000000 0x35fe0fff8e000000 0x1aff07ffc7000000

def z981 : W := mkw 0x0002363144294710 0x00011b18a214a388 0xbe867e7fce7fcf99 0x5f433f3fe73fe7cc

def z982 : W := mkw 0xee23fe217e097e18 0x7711ff10bf04bf0c 0x8801fe007e007e18 0x4400ff003f003f0c

def z983 : W := mkw 0x8befee0001db7c00 0x45f7f70000edbe00 0x03fff00001fffe00 0x01fff80000ffff00

def z984 : W := mkw 0x5df7fdeb7d400040 0x2efbfef5bea00020 0x3dffffffff800060 0x9effffffffc00030

def z985 : W := mkw 0x301010bfc62483b8 0x9808085fe31241dc 0x8400007fce000199 0x4200003fe70000cc

def z986 : W := mkw 0x15dd41dea1f681e0 0x8aeea0ef50fb40f0 0x37ff81ffb1ff81e1 0x9bffc0ffd8ffc0f0

def z987 : W := mkw 0x5ff7fdeb7c002804 0x2ffbfef5be001402 0x7dfffffffe003006 0x3effffffff001803

def z988 : W := mkw 0x2008021483ffd7fa 0x9004010a41ffebfd 0xc200000001ffffff 0xe100000000ffffff

def z989 : W := mkw 0xce23fe2164097c00 0x6711ff10b204be00 0x0801fe0000007e00 0x0400ff0000003f00

def z990 : W := mkw 0x11d401de802481e0 0x88ea00ef401240f0 0x37fe01ff807f81e1 0x9bff00ffc03fc0f0

def z991 : W := mkw 0x5ff7fdeb7c002800 0x2ffbfef5be001400 0x3dfffffffe007e00 0x1effffffff003f00

def z992 : W := mkw 0x11dc01ca00920000 0x08ee00e500490000 0x35fe01ff801f8000 0x1aff00ffc00fc000

def z993 : W := mkw 0x5432bdeb7c000000 0x2a195ef5be000000 0x3dfffffffe000000 0x1effffffff000000

def z994 : W := mkw 0x5df7fdeb7d400000 0x2efbfef5bea00000 0x3fffffffffe00000 0x1ffffffffff00000

def z995 : W := mkw 0x2022be215e09561a 0x10115f10af04ab0d 0x88007e004e004e18 0x44003f002700270c

def z996 : W := mkw 0x0200103041602b54 0x0100081820b015aa 0xef81f1f071e07fff 0xf7c0f8f838f03fff

def z997 : W := mkw 0x13dd41de81f6a9e0 0x89eea0ef40fb54f0 0x37ff81ff81ffb1e1 0x9bffc0ffc0ffd8f0

def z998 : W := mkw 0x7df7fdeb7c010610 0x3efbfef5be008308 0x3dfffffffe000e00 0x1effffffff000700

def z999 : W := mkw 0x8a6eae0001db7c00 0x4537570000edbe00 0x3afe7e0001fffe00 0x1d7f3f0000ffff00

def z1000 : W := mkw 0x6c23fe217e094408 0x3611ff10bf04a204 0x0801fe007e000000 0x0400ff003f000000

def z1001 : W := mkw 0x00308a8c1a0c4088 0x001845460d062044 0xff798f8c7f9c71ff 0xffbcc7c63fce38ff

def z1002 : W := mkw 0x24023635e62dc79c 0x12011b1af316e3ce 0xfe867e7ffe7fcf9f 0x7f433f3fff3fe7cf

def z1003 : W := mkw 0x11dc01ce809680a0 0x88ee00e7404b4050 0x37fe01ff819f81e1 0x9bff00ffc0cfc0f0

def z1004 : W := mkw 0x5ff7fdeb7d402a54 0x2ffbfef5bea0152a 0xfdffffffff807e7e 0xfeffffffffc03f3f

def z1005 : W := mkw 0x8befee0001db7c00 0x45f7f70000edbe00 0x3afe7e00007fce00 0x1d7f3f00003fe700

def z1006 : W := mkw 0xa208021483ffffdc 0x5104010a41ffffee 0xc200000001ffffff 0xe100000000ffffff

def z1007 : W := mkw 0x2623fe217e097e1e 0x1311ff10bf04bf0f 0xc801fe007e007e1e 0x6400ff003f003f0f

def z1008 : W := mkw 0x8befee0001db7c00 0x45f7f70000edbe00 0x0b79fe0001fffe00 0x05bcff0000ffff00

def z1009 : W := mkw 0x8befee0001db7c00 0x45f7f70000edbe00 0x3fffff8071fffe00 0x1fffffc038ffff00

def z1010 : W := mkw 0x59f7edcb1c000000 0x2cfbf6e58e000000 0x3dffffff8e000000 0x1effffffc7000000

def z1011 : W := mkw 0x0781517061602b54 0x03c0a8b830b015aa 0xcd01f1f071807fff 0xe680f8f838c03fff

def z1012 : W := mkw 0x20023635c62dc798 0x10011b1ae316e3cc 0x92867e7f8e7fcf99 0x49433f3fc73fe7cc

def z1013 : W := mkw 0x11cc015681f681e0 0x88e600ab40fb40f0 0x33fe007381ff81e1 0x99ff0039c0ffc0f0

def z1014 : W := mkw 0x5df7fdeb7c000000 0x2efbfef5be000000 0x3fffffffff807000 0x1fffffffffc03800

def z1015 : W := mkw 0x0581517060200310 0x02c0a8b830100188 0xef81f1f071e07fff 0xf7c0f8f838f03fff

def z1016 : W := mkw 0x5ff7fdeb7d402a14 0x2ffbfef5bea0150a 0xffffffffffe07e1e 0x7ffffffffff03f0f

def z1017 : W := mkw 0x5c33fdeb7c000000 0x2e19fef5be000000 0x3d79fffffe000000 0x1ebcffffff000000

def z1018 : W := mkw 0x105c009e80b681a0 0x882e004f405b40d0 0x147e007f801f8181 0x0a3f003fc00fc0c0

def z1019 : W := mkw 0x11dc01da81f28140 0x88ee00ed40f940a0 0x37fe01ff81ff8000 0x1bff00ffc0ffc000

def z1020 : W := mkw 0x00388a8c9a9cd0aa 0x001c45464d4e6855 0xff7f8f8fff9ff1ff 0xffbfc7c7ffcff8ff

def z1021 : W := mkw 0x2008021483ffc798 0x1004010a41ffe3cc 0x8200000001ffcf99 0x4100000000ffe7cc

def z1022 : W := mkw 0xdfefef4221db7c00 0x6ff7f7a110edbe00 0x3bfffe0001fffe00 0x1dffff0000ffff00

def z1023 : W := mkw 0x241011fdfe2483fe 0x120808feff1241ff 0xc40001fffe0001ff 0xe20000ffff0000ff

def z1024 : W := mkw 0x00288a001a98500a 0x001445000d4c2805 0xff798f807f9c71ff 0xffbcc7c03fce38ff

def z1025 : W := mkw 0xdffdc9ca39d23844 0x6ffee4e51ce91c22 0x4179818031803066 0xa0bcc0c018c01833

def z1026 : W := mkw 0x13dc01de81f6abf4 0x89ee00ef40fb55fa 0x37fe01ff81ff8fe1 0x9bff00ffc0ffc7f0

def z1027 : W := mkw 0x00388a8c1a9c50aa 0x001c45460d4e2855 0xd5798f8c7f9c31ff 0xeabcc7c63fce18ff

def z1028 : W := mkw 0x5ff7fdeb7c002a14 0x2ffbfef5be00150a 0xffffffffff807fff 0xffffffffffc03fff

def z1029 : W := mkw 0x07815170e160ab54 0x03c0a8b870b055aa 0xef87f1f3f1e3ffff 0xf7c3f8f9f8f1ffff

def z1030 : W := mkw 0x01c6260000094400 0x00e313000004a200 0x3bfe7e00007fce00 0x1dff3f00003fe700

def z1031 : W := mkw 0x0601517060202b54 0x0300a8b8301015aa 0xef01f1f071807fff 0xf780f8f838c03fff

def z1032 : W := mkw 0x03cf660001db6c00 0x01e7b30000edb600 0x3bfffe0001fffe00 0x1dffff0000ffff00

def z1033 : W := mkw 0x0030888818000000 0x001844440c000000 0x3dff8ffffe000000 0x1effc7ffff000000

def z1034 : W := mkw 0x5df7fdeb7c000000 0x2efbfef5be000000 0xbffffffffe004199 0x5fffffffff0020cc

def z1035 : W := mkw 0x20023625c60dc488 0x10011b12e306e244 0x3e867e7fce7fce00 0x1f433f3fe73fe700

def z1036 : W := mkw 0x17fdc9ca39d23866 0x8bfee4e51ce91c33 0x4179818031803066 0xa0bcc0c018c01833

def z1037 : W := mkw 0x09efee0001db4400 0x04f7f70000eda200 0x3bfffe0001ffce00 0x1dffff0000ffe700

def z1038 : W := mkw 0xdbefee0305db7c00 0x6df7f70182edbe00 0x3bfffe0381fffe00 0x1dffff01c0ffff00

def z1039 : W := mkw 0x5876bcab5c000000 0x2c3b5e55ae000000 0x3dfffffffe000000 0x1effffffff000000

def z1040 : W := mkw 0x5ff7fdeb7c002a14 0x2ffbfef5be00150a 0x3dfffffffe000e00 0x1effffffff000700

def z1041 : W := mkw 0x8bcf660001db6c00 0x45e7b30000edb600 0x3bfe7e0001ffce00 0x1dff3f0000ffe700

def z1042 : W := mkw 0x0781414021402844 0x03c0a0a010a01422 0xef81f18071e07fff 0xf7c0f8c038f03fff

def z1043 : W := mkw 0x0038888818901022 0x001c44440c480811 0xff798f8c7f8071ff 0xffbcc7c63fc038ff

def z1044 : W := mkw 0x203aae8d1e9d54aa 0x101d57468f4eaa55 0x10780e0c0e1c0000 0x083c0706070e0000

def z1045 : W := mkw 0x8befee0001db7c22 0x45f7f70000edbe11 0x7bfffe0001fffe66 0xbdffff0000ffff33

def z1046 : W := mkw 0x00022614822dc588 0x0001130a4116e2c4 0xbe867e7fce7fcf99 0x5f433f3fe73fe7cc

def z1047 : W := mkw 0x0008021482bcd1ea 0x8004010a415e68f5 0xc2000000019c71ff 0xe100000000ce38ff

def z1048 : W := mkw 0xdfc7757365632f54 0x6fe3bab9b2b197aa 0x0086707380638e00 0x00433839c031c700

def z1049 : W := mkw 0x0781517061602b54 0x03c0a8b830b015aa 0xc381f1f031e07fff 0xe1c0f8f818f03fff

def z1050 : W := mkw 0x11d401de816681c0 0x88ea00ef40b340e0 0x37fe01ff807f8181 0x1bff00ffc03fc0c0

def z1051 : W := mkw 0xcbefee011ddb7c00 0x65f7f7008eedbe00 0x3bfffe000ffffe00 0x1dffff0007ffff00

def z1052 : W := mkw 0x003aae8c1a9d54aa 0x001d57460d4eaa55 0x107e0e0c0e1f8000 0x083f0706070fc000

def z1053 : W := mkw 0x4c23fe217c094400 0x2611ff10be04a200 0x0801fe007e004e00 0x0400ff003f002700

def z1054 : W := mkw 0xddf7fdeb7c030400 0x6efbfef5be018200 0x3dfffffffe038000 0x1effffffff01c000

def z1055 : W := mkw 0x8bcf640001d32c00 0x45e7b20000e99600 0x10fe7000007f8e00 0x087f3800003fc700

def z1056 : W := mkw 0x11f6bdeb5c000000 0x08fb5ef5ae000000 0x3dfffffffe000000 0x1effffffff000000

def z1057 : W := mkw 0x9bfdc9ca19d23862 0xcdfee4e50ce91c31 0x4179818031803066 0xa0bcc0c018c01833

def z1058 : W := mkw 0x83cd420001db7c00 0x41e6a10000edbe00 0x3bfff00001fffe00 0x1dfff80000ffff00

def z1059 : W := mkw 0x0030888c1a0400aa 0x001844460d020055 0xff798f8c7f8071ff 0xffbcc7c63fc038ff

def z1060 : W := mkw 0x0781517061602b54 0x03c0a8b830b015aa 0xcb01f18071e07fff 0xe580f8c038f03fff

def z1061 : W := mkw 0x8befec0001d32c00 0x45f7f60000e99600 0x3bfffe0001ff8e00 0x1dffff0000ffc700

def z1062 : W := mkw 0x00023625460d4488 0x00011b12a306a244 0xbe867e7fce7fcf99 0x5f433f3fe73fe7cc

def z1063 : W := mkw 0x01c4001480248180 0x00e2000a401240c0 0x37fe007f807f8181 0x1bff003fc03fc0c0

def z1064 : W := mkw 0x8befee0001db7c00 0x45f7f70000edbe00 0x11fffe0001ffbe00 0x08ffff0000ffdf00

def z1065 : W := mkw 0x822aae0001db7c00 0x4115570000edbe00 0x3bfffe0001fffe00 0x1dffff0000ffff00

def z1066 : W := mkw 0x11dc01de81f68180 0x08ee00ef40fb40c0 0x37fe01ff81ff8181 0x1bff00ffc0ffc0c0

def z1067 : W := mkw 0x55dc01deb9f681e0 0xaaee00ef5cfb40f0 0x37fe01ffb1ff81e1 0x9bff00ffd8ffc0f0

def z1068 : W := mkw 0x101801de80b481e0 0x880c00ef405a40f0 0x37fe01ff81ff81e1 0x9bff00ffc0ffc0f0

def z1069 : W := mkw 0x0000102040000210 0x0000081020000108 0xef01f18071807fff 0xf780f8c038c03fff

def z1070 : W := mkw 0x20023635c62dc798 0x10011b1ae316e3cc 0x36867e7f8e7f8f81 0x1b433f3fc73fc7c0

def z1071 : W := mkw 0x0018009c81f681e0 0x800c004e40fb40f0 0x37fe01ff81ff81e1 0x9bff00ffc0ffc0f0

def z1072 : W := mkw 0xa008021482bfd798 0x5004010a415febcc 0x82000000007fcf99 0x41000000003fe7cc

def z1073 : W := mkw 0x55b1d9eb7c000000 0x2ad8ecf5be000000 0x3df9fffffe000000 0x1efcffffff000000

def z1074 : W := mkw 0x15dc01dea1f681e4 0x8aee00ef50fb40f2 0x77fe01ffb1ff81e7 0xbbff00ffd8ffc0f3

def z1075 : W := mkw 0x19f7fdeb44000000 0x0cfbfef5a2000000 0x3dffffffce000000 0x1effffffe7000000

def z1076 : W := mkw 0x59f6adcb1c000000 0x2cfb56e58e000000 0x10fe0e7f8e000000 0x087f073fc7000000

def z1077 : W := mkw 0x11dc01de81f681e0 0x88ee00ef40fb40f0 0x3ffe0fffcfff81e1 0x9fff07ffe7ffc0f0

def z1078 : W := mkw 0x8befee0105db7c00 0x45f7f70082edbe00 0x3bfffe0f8ffffe00 0x1dffff07c7ffff00

def z1079 : W := mkw 0x00001234c22cc398 0x0000091a611661cc 0xbe867e7fce7fcf99 0x5f433f3fe73fe7cc

def z1080 : W := mkw 0x03edca0001da7800 0x01f6e50000ed3c00 0x3bfffe0001fffe00 0x1dffff0000ffff00

def z1081 : W := mkw 0x5fc5517261602b54 0x2fe2a8b930b015aa 0xef81f1f071e07fff 0xf7c0f8f838f03fff

def z1082 : W := mkw 0x5ddd41dea1f681e0 0xaeeea0ef50fb40f0 0x37fe01ff81ff81e1 0x9bff00ffc0ffc0f0

def z1083 : W := mkw 0x0781517061602b54 0x03c0a8b830b015aa 0xff87f1fff1e07fff 0xffc3f8fff8f03fff

def z1084 : W := mkw 0x17dd41dea1f6a9e4 0x8beea0ef50fb54f2 0x7ffff1ffb1ffffe7 0xbffff8ffd8fffff3

def z1085 : W := mkw 0x03cd400001d22800 0x01e6a00000e91400 0x33fe700001ff8e00 0x19ff380000ffc700

def z1086 : W := mkw 0x0601503061602b54 0x0300a81830b015aa 0xef01f18071e07fff 0xf780f8c038f03fff

def z1087 : W := mkw 0x11dc01de9bf681ea 0x88ee00ef4dfb40f5 0xffff81fffffff1ff 0xffffc0fffffff8ff

def z1088 : W := mkw 0x741011fffe2483f8 0xba0808ffff1241fc 0x840001fffe0001f9 0xc20000ffff0000fc

def z1089 : W := mkw 0x00288a04029c5088 0x00144502014e2844 0xff798f8c7f9c71ff 0xffbcc7c63fce38ff

def z1090 : W := mkw 0x11dc01ce81d680e0 0x88ee00e740eb4070 0x35fe01ff819f8060 0x9aff00ffc0cfc030

def z1091 : W := mkw 0x13dc01de81f6a9e4 0x89ee00ef40fb54f2 0x77fe01ff81ffb1e7 0xbbff00ffc0ffd8f3

def z1092 : W := mkw 0x5ff7fdeb7d402844 0x2ffbfef5bea01422 0x3dfffffffe000000 0x1effffffff000000

def z1093 : W := mkw 0x11dc01de81f681e0 0x88ee00ef40fb40f0 0x33fe007f81ff8000 0x19ff003fc0ffc000

def z1094 : W := mkw 0x20023635c62dc7ba 0x10011b1ae316e3dd 0xfe867e7fce7fcfff 0xff433f3fe73fe7ff

def z1095 : W := mkw 0x00388a8c1a9c50aa 0x001c45460d4e2855 0xffff8fffff9c71ff 0xffffc7ffffce38ff

def z1096 : W := mkw 0x20023635c62dc7f8 0x90011b1ae316e3fc 0xbe867e7fce7fcff9 0xdf433f3fe73fe7fc

def z1097 : W := mkw 0x105634ab44000000 0x082b1a55a2000000 0x3cfe7e7fce000000 0x1e7f3f3fe7000000

def z1098 : W := mkw 0x11dc01de81f681e0 0x88ee00ef40fb40f0 0xbffe01ffc1ffc1f9 0xdfff00ffe0ffe0fc

def z1099 : W := mkw 0x17dd41dea1f6a9e4 0x8beea0ef50fb54f2 0x37fe01ff81ff81e1 0x9bff00ffc0ffc0f0

def z1100 : W := mkw 0x17c5517261602b54 0x0be2a8b930b015aa 0xef87f1f3f1e07fff 0xf7c3f8f9f8f03fff

def z1101 : W := mkw 0x0022bc2144000000 0x00115e10a2000000 0x3dfffe7fce000000 0x1effff3fe7000000

def z1102 : W := mkw 0xabefee0107db7c08 0x55f7f70083edbe04 0x3bfffe000ffffe00 0x1dffff0007ffff00

def z1103 : W := mkw 0x11dc01de80b681e0 0x88ee00ef405b40f0 0x35fe01ff801f81e1 0x9aff00ffc00fc0f0

def z1104 : W := mkw 0x5df7fdeb7c000000 0x2efbfef5be000000 0x3fffffffff8001e1 0x9fffffffffc000f0

def z1105 : W := mkw 0xa208021483ffffba 0x5104010a41ffffdd 0xc200000001ffffff 0xe100000000ffffff

def z1106 : W := mkw 0x2002362146094618 0x10011b10a304a30c 0xbe867e7fce7fce18 0x5f433f3fe73fe70c

def z1107 : W := mkw 0x5df7fdeb7c000000 0x2efbfef5be000000 0x35fe7fff8e000000 0x1aff3fffc7000000

def z1108 : W := mkw 0x5c76bdeb7c000000 0x2e3b5ef5be000000 0x3d7f8ffffe000000 0x1ebfc7ffff000000

def z1109 : W := mkw 0x89efee00009b5400 0x44f7f700004daa00 0x3bfffe00007fce00 0x1dffff00003fe700

def z1110 : W := mkw 0x00308a881a08500a 0x001845440d042805 0xff798f8c7f8071ff 0xffbcc7c63fc038ff

def z1111 : W := mkw 0x6c23fe217e09561a 0x3611ff10bf04ab0d 0xc801fe007e007e1e 0x6400ff003f003f0f

def z1112 : W := mkw 0x8befee0003db7c08 0x45f7f70001edbe04 0xbbfffe004ffffe18 0x5dffff0027ffff0c

def z1113 : W := mkw 0x5df7fdeb7c000044 0x2efbfef5be000022 0x7dfffffffe000066 0xbeffffffff000033

def z1114 : W := mkw 0x8fefef4021db7c00 0x47f7f7a010edbe00 0x3bffff8031fffe00 0x1dffffc018ffff00

def z1115 : W := mkw 0x55d635eb7c000000 0x2aeb1af5be000000 0x3dfe7ffffe000000 0x1eff3fffff000000

def z1116 : W := mkw 0x00388a8c1a9d54aa 0x001c45460d4eaa55 0xff798f8c7fffffff 0xffbcc7c63fffffff

def z1117 : W := mkw 0x5df7fdeb7c000000 0x2efbfef5be000000 0x18fffe7ffe000000 0x0c7fff3fff000000

def z1118 : W := mkw 0x103089ca18000000 0x081844e50c000000 0x3d798ffffe000000 0x1ebcc7ffff000000

def z1119 : W := mkw 0x5df5c9ca38000000 0x2efae4e51c000000 0x3dff8ffffe000000 0x1effc7ffff000000

def z1120 : W := mkw 0x5fc77573e562ab54 0xafe3bab9f2b155aa 0x0086707380638e00 0x00433839c031c700

def z1121 : W := mkw 0xdffdc9ca39d23822 0x6ffee4e51ce91c11 0x4179818031803066 0xa0bcc0c018c01833

def z1122 : W := mkw 0x00023435c4248390 0x00011a1ae21241c8 0xbe867e7fce7fcf99 0x5f433f3fe73fe7cc

def z1123 : W := mkw 0x11dc01de99f681e2 0x88ee00ef4cfb40f1 0x77fe01ffb1ff81e7 0xbbff00ffd8ffc0f3

def z1124 : W := mkw 0x105c009e80b681a0 0x882e004f405b40d0 0x37fe01ff81ff81e1 0x9bff00ffc0ffc0f0

def z1125 : W := mkw 0xaa23fe215e097e1a 0x5511ff10af04bf0d 0xc801fe007e007e1e 0x6400ff003f003f0f

def z1126 : W := mkw 0x541011fffc2483f4 0xaa0808fffe1241fa 0xc40001fffe0001ff 0xe20000ffff0000ff

def z1127 : W := mkw 0x5df7fdeb7c000000 0x2efbfef5be000000 0x3ffffffffe604e00 0x1fffffffff302700

def z1128 : W := mkw 0x8befee0001db7c00 0x45f7f70000edbe00 0x33fe7e0001ff8e00 0x19ff3f0000ffc700

def z1129 : W := mkw 0x8befee0001db7c00 0x45f7f70000edbe00 0x7bffff8031fffe66 0xbdffffc018ffff33

def z1130 : W := mkw 0x019801dc81f481e0 0x00cc00ee40fa40f0 0x37fe01ff81ff81e1 0x9bff00ffc0ffc0f0

def z1131 : W := mkw 0x2022be2146095618 0x10115f10a304ab0c 0x8801fe004e007e18 0x4400ff0027003f0c

def z1132 : W := mkw 0x11dc01ca01d20060 0x88ee00e500e90030 0x37fe01ff81ff8060 0x9bff00ffc0ffc030

def z1133 : W := mkw 0x8fefee0021db7c04 0x47f7f70010edbe02 0x7bfffe0031fffe06 0x3dffff0018ffff03

def z1134 : W := mkw 0x5876ac8b1c000000 0x2c3b56458e000000 0x34fe0e7f8e000000 0x1a7f073fc7000000

def z1135 : W := mkw 0x8be7ee0000097c00 0x45f3f7000004be00 0x3bfffe00007ffe00 0x1dffff00003fff00

def z1136 : W := mkw 0x11dc01de81f681e0 0x88ee00ef40fb40f0 0x14fe01ff807f81e1 0x8a7f00ffc03fc0f0

def z1137 : W := mkw 0x17c5517261622b54 0x8be2a8b930b115aa 0xef81f1f071e07fff 0xf7c0f8f838f03fff

def z1138 : W := mkw 0x105c01de80b681e0 0x882e00ef405b40f0 0x36fe01ff807f81e1 0x9b7f00ffc03fc0f0

def z1139 : W := mkw 0x20023635c62dc798 0x10011b1ae316e3cc 0xfe87fe7ffe7fff9f 0x7f43ff3fff3fffcf

def z1140 : W := mkw 0x00388a8c9a9ed0aa 0x801c45464d4f6855 0xff798f8c7f9ff1ff 0xffbcc7c63fcff8ff

def z1141 : W := mkw 0x0781517061602b54 0x03c0a8b830b015aa 0xff81fffc7fe07fff 0xffc0fffe3ff03fff

def z1142 : W := mkw 0x9bdd41de81f6a9e0 0xcdeea0ef40fb54f0 0x37fe01ff81ff81e1 0x9bff00ffc0ffc0f0

def z1143 : W := mkw 0x00388a881a98502a 0x001c45440d4c2815 0xef798f807f8071ff 0xf7bcc7c03fc038ff

def z1144 : W := mkw 0x0008001480b48180 0x0004000a405a40c0 0x37fe007f81ff8181 0x1bff003fc0ffc0c0

def z1145 : W := mkw 0x13dc01de81f6a9e0 0x89ee00ef40fb54f0 0x37fe01ff81ffffe1 0x9bff00ffc0fffff0

def z1146 : W := mkw 0x11cc015281f28140 0x88e600a940f940a0 0x10fe0073807f8000 0x087f0039c03fc000

def z1147 : W := mkw 0x5876bcab5c000000 0x2c3b5e55ae000000 0x147e0e7fce000000 0x0a3f073fe7000000

def z1148 : W := mkw 0x0befec0001d22800 0x05f7f60000e91400 0x3bfffe0001fffe00 0x1dffff0000ffff00

def z1149 : W := mkw 0x01cc015481f681c0 0x00e600aa40fb40e0 0x37fe01ff81ff81e1 0x9bff00ffc0ffc0f0

def z1150 : W := mkw 0xce23fe217c097e14 0x6711ff10be04bf0a 0xc801fe007e007e1e 0x6400ff003f003f0f

def z1151 : W := mkw 0x11dc01de81f683f0 0x88ee00ef40fb41f8 0xb7fe01ff81ffcff9 0xdbff00ffc0ffe7fc

def z1152 : W := mkw 0x9befef4201db7c00 0x4df7f7a100edbe00 0x3bfffe7381fffe00 0x1dffff39c0ffff00

def z1153 : W := mkw 0x00023635c42dc580 0x00011b1ae216e2c0 0x3e867e7fce7fcf81 0x1f433f3fe73fe7c0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z7,z5,z6]),(0,[z0,z1,z3,z8,z4,z5,z6]),(0,[z0,z9,z1,z3,z4,z5,z6])],[(0,[z10,z0,z11,z3,z4,z5,z6]),(1,[z0,z1,z12,z4,z5,z6]),(0,[z0,z1,z3,z4,z13,z5,z6]),(0,[z14,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z15,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z6]),(0,[z0,z1,z3,z4,z5,z6,z16]),(0,[z0,z1,z3,z4,z17,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z18])],[(0,[z19,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z20,z4,z5,z6]),(0,[z21,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z22]),(0,[z0,z23,z1,z24,z4,z5,z6]),(0,[z0,z1,z3,z25,z4,z5,z6]),(0,[z0,z1,z3,z26,z4,z5,z6]),(0,[z0,z23,z27,z1,z3,z4,z5]),(1,[z0,z1,z3,z28,z29,z6])],[(0,[z0,z1,z3,z4,z30,z5,z6]),(0,[z31,z0,z1,z3,z13,z5,z6]),(0,[z32,z0,z1,z3,z4,z5,z6])],[],[(0,[z0,z1,z3,z4,z5,z6,z33]),(0,[z34,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z35,z3,z4,z5,z36]),(0,[z0,z37,z1,z3,z4,z5,z6]),(0,[z0,z1,z38,z3,z4,z5,z6])]],
   [[(1,[z0,z1,z4,z39,z5,z6]),(0,[z40,z41,z0,z1,z3,z4,z6])],[(0,[z0,z42,z1,z3,z4,z5,z6]),(0,[z43,z0,z1,z3,z4,z5,z44]),(0,[z0,z1,z3,z4,z5,z45,z6])],[(0,[z0,z1,z46,z3,z4,z5,z6])],[(0,[z0,z47,z1,z3,z4,z5,z6]),(0,[z0,z1,z48,z3,z4,z5,z6]),(0,[z41,z0,z1,z3,z4,z49,z6]),(0,[z0,z1,z50,z3,z4,z51,z6]),(0,[z0,z1,z52,z3,z4,z5,z6])],[(0,[z53,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z54,z4,z5,z6]),(0,[z43,z40,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z55])],[(0,[z0,z56,z1,z3,z4,z5,z6]),(0,[z57,z0,z1,z3,z4,z58,z6]),(0,[z0,z1,z3,z59,z4,z5,z6]),(0,[z60,z0,z1,z3,z4,z5,z36]),(0,[z0,z1,z3,z4,z5,z61,z6]),(0,[z0,z1,z62,z3,z28,z4,z6]),(0,[z0,z1,z63,z3,z4,z5,z6]),(0,[z43,z0,z1,z64,z3,z4,z5])],[(0,[z65,z0,z1,z3,z4,z5,z6]),(1,[z0,z66,z3,z4,z5,z67]),(0,[z68,z0,z1,z4,z51,z5,z6])],[(0,[z69,z0,z3,z4,z13,z5,z6]),(0,[z0,z1,z3,z4,z5,z70,z6]),(0,[z0,z71,z1,z3,z4,z5,z6])]],
   [[(0,[z72,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z35,z3,z4,z5,z73]),(0,[z0,z1,z3,z74,z5,z75,z6])],[(0,[z0,z76,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z77,z6]),(0,[z0,z1,z3,z28,z4,z29,z6])],[(0,[z78,z0,z1,z3,z4,z5,z6]),(0,[z79,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z80]),(0,[z0,z1,z3,z4,z81,z5,z6])],[(0,[z0,z1,z3,z4,z5,z82,z6]),(0,[z0,z1,z3,z83,z4,z5,z6]),(0,[z57,z1,z3,z4,z5,z58,z6]),(0,[z43,z60,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z84,z6]),(0,[z0,z1,z3,z4,z5,z85,z6]),(0,[z86,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z87,z5,z6])],[(0,[z0,z1,z88,z3,z4,z5,z6]),(0,[z0,z89,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z90]),(0,[z43,z0,z1,z3,z5,z6,z44])],[(0,[z0,z0,z1,z3,z4,z5,z6]),(0,[z91,z0,z1,z24,z4,z5,z6]),(0,[z92,z0,z1,z3,z4,z5,z6]),(0,[z93,z0,z1,z3,z28,z4,z6])],[(0,[z0,z1,z3,z4,z94,z5,z6]),(0,[z0,z95,z1,z3,z4,z5,z6]),(0,[z0,z1,z96,z3,z4,z5,z6])],[(0,[z0,z1,z24,z97,z4,z5,z6]),(0,[z68,z98,z0,z1,z4,z5,z6]),(1,[z0,z3,z4,z5,z99,z6]),(0,[z0,z100,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z101,z5,z6])]],
   [[(0,[z102,z0,z1,z3,z4,z5,z6]),(0,[z0,z103,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z104]),(0,[z43,z0,z1,z3,z4,z5,z6]),(0,[z0,z105,z1,z4,z5,z6,z44]),(0,[z106,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z3,z4,z5,z6]),(0,[z91,z1,z3,z24,z4,z5,z6]),(0,[z107,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z108,z5,z6]),(0,[z0,z1,z35,z97,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z109,z6]),(0,[z0,z1,z3,z4,z110,z5,z6]),(0,[z111,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z112,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z113]),(0,[z114,z0,z1,z3,z4,z5,z6])],[(0,[z10,z0,z1,z3,z4,z115,z6]),(0,[z0,z1,z3,z4,z5,z116,z6]),(0,[z0,z1,z3,z4,z117,z5,z6]),(0,[z118,z0,z1,z3,z4,z5,z6]),(0,[z119,z0,z27,z3,z4,z5,z6]),(0,[z120,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z121,z6]),(0,[z0,z122,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z110,z6])],[(0,[z0,z1,z3,z4,z123,z5,z6]),(0,[z0,z124,z1,z3,z4,z5,z6]),(0,[z0,z1,z125,z3,z4,z5,z6])],[(0,[z0,z1,z3,z126,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z127,z6]),(0,[z0,z1,z3,z4,z5,z6,z128]),(0,[z0,z1,z3,z4,z5,z129,z6])],[(0,[z119,z0,z3,z4,z5,z67,z6]),(0,[z0,z1,z3,z4,z130,z5,z6]),(0,[z0,z1,z3,z131,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z132]),(0,[z0,z1,z3,z4,z5,z6,z133])],[(0,[z0,z1,z3,z4,z5,z80,z134]),(0,[z0,z1,z135,z4,z5,z6,z136])]],
   [[(0,[z137,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z138,z4,z6]),(0,[z0,z1,z3,z4,z139,z6,z136]),(0,[z0,z1,z3,z4,z5,z6,z140])],[(0,[z10,z1,z88,z3,z4,z5,z6]),(0,[z141,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z142,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z143,z144,z6]),(0,[z0,z1,z3,z4,z145,z5,z6])],[(0,[z10,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z146,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z147]),(0,[z0,z1,z3,z4,z148,z5,z6])],[(0,[z0,z1,z3,z4,z5,z149,z6]),(0,[z0,z1,z3,z4,z150,z5,z6]),(1,[z0,z1,z3,z4,z5,z151]),(0,[z0,z1,z3,z4,z5,z152,z6])],[(0,[z0,z1,z3,z153,z4,z5,z6]),(0,[z154,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z155,z6])],[(1,[z0,z1,z3,z4,z5,z156]),(0,[z0,z1,z3,z4,z5,z6,z157]),(0,[z158,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z159,z3,z4,z5,z6])],[(1,[z0,z1,z3,z4,z160,z6]),(0,[z0,z161,z1,z3,z4,z5,z6]),(0,[z0,z27,z1,z3,z4,z110,z6])],[(0,[z162,z0,z1,z3,z4,z5,z6]),(0,[z93,z57,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z6,z163]),(0,[z164,z0,z1,z3,z4,z5,z6]),(0,[z93,z0,z1,z3,z4,z139,z6]),(0,[z0,z1,z165,z3,z51,z5,z6])]],
   [[(0,[z0,z166,z1,z3,z4,z5,z6]),(0,[z167,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z168,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z145,z169,z6])],[(0,[z1,z170,z3,z24,z4,z5,z6]),(0,[z0,z66,z1,z3,z4,z5,z67])],[(0,[z0,z171,z1,z3,z4,z5,z6]),(0,[z172,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z173,z5,z6])],[(0,[z0,z174,z1,z3,z4,z5,z6])],[(0,[z0,z1,z4,z39,z13,z5,z6]),(0,[z175,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z176,z5,z6])],[(0,[z0,z1,z3,z4,z5,z58,z6]),(0,[z0,z1,z3,z4,z177,z5,z6]),(0,[z0,z1,z3,z4,z178,z5,z6])],[(0,[z98,z1,z170,z3,z4,z5,z6]),(0,[z0,z1,z64,z3,z4,z5,z136]),(0,[z0,z1,z3,z4,z179,z5,z6])],[(0,[z180,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z181,z4,z5,z6]),(0,[z0,z1,z3,z4,z182,z51,z6]),(0,[z183,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z184,z6])],[(0,[z0,z1,z3,z4,z185,z5,z6]),(0,[z0,z1,z186,z3,z4,z5,z6]),(0,[z187,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z188,z5,z6]),(0,[z68,z0,z1,z3,z51,z5,z6]),(0,[z0,z1,z3,z74,z4,z5,z6]),(1,[z0,z1,z135,z4,z5,z6])],[(0,[z119,z0,z3,z189,z4,z5,z6]),(0,[z0,z190,z1,z3,z4,z5,z6]),(0,[z191,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z192,z4,z5,z6])],[(0,[z41,z0,z1,z62,z3,z4,z6]),(0,[z0,z1,z193,z3,z4,z5,z6]),(1,[z0,z1,z194,z4,z5,z6]),(0,[z195,z0,z1,z3,z4,z5,z6]),(0,[z196,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z197,z5,z6])],[(0,[z0,z1,z3,z4,z5,z198,z6]),(0,[z0,z199,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z200]),(0,[z0,z1,z3,z74,z4,z5,z134])],[(0,[z98,z0,z1,z24,z4,z5,z6]),(0,[z201,z0,z1,z3,z4,z5,z6]),(0,[z202,z0,z124,z3,z4,z5,z6]),(0,[z0,z203,z1,z3,z4,z5,z6]),(0,[z204,z0,z1,z3,z4,z5,z6]),(0,[z0,z205,z1,z3,z4,z5,z6]),(0,[z0,z1,z206,z3,z4,z5,z6])],[(0,[z0,z1,z3,z207,z4,z5,z6]),(0,[z0,z1,z3,z4,z208,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z209]),(0,[z0,z1,z3,z4,z5,z6,z210]),(0,[z0,z1,z62,z3,z4,z211,z6]),(0,[z0,z1,z125,z3,z4,z6,z44])],[(0,[z10,z57,z1,z3,z4,z5,z6]),(0,[z212,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z213,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z67,z6]),(1,[z0,z1,z3,z4,z214,z5]),(0,[z43,z0,z23,z1,z3,z4,z5]),(0,[z40,z0,z1,z64,z3,z4,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z215,z6]),(0,[z0,z1,z3,z189,z25,z5,z6]),(0,[z41,z0,z1,z3,z4,z6,z136]),(0,[z0,z1,z3,z4,z5,z216,z6]),(0,[z0,z124,z1,z3,z4,z217,z6]),(0,[z0,z1,z218,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z219,z5,z6]),(0,[z43,z0,z1,z3,z74,z5,z6])],[(0,[z119,z0,z3,z97,z4,z5,z6]),(0,[z0,z1,z3,z138,z24,z4,z6]),(0,[z41,z1,z3,z4,z49,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z220]),(0,[z93,z0,z1,z62,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z221,z6]),(0,[z0,z1,z3,z222,z4,z5,z6]),(1,[z0,z223,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z224,z5,z6]),(1,[z0,z225,z3,z4,z169,z6]),(0,[z226,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z227,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z228,z5,z6]),(0,[z229,z0,z1,z3,z4,z5,z6]),(1,[z93,z0,z1,z4,z211,z6])],[(0,[z1,z3,z4,z49,z5,z58,z6]),(0,[z0,z1,z3,z230,z4,z5,z6]),(0,[z0,z1,z231,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z145,z139,z6]),(0,[z0,z1,z232,z3,z4,z5,z6])],[(0,[z233,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z234,z5,z6]),(0,[z0,z1,z3,z4,z235,z5,z6]),(0,[z93,z0,z1,z3,z4,z211,z6])],[(0,[z0,z1,z3,z4,z5,z6,z236]),(0,[z0,z1,z3,z4,z5,z237,z6]),(0,[z0,z105,z1,z3,z4,z5,z6])]],
   [[(0,[z238,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z182,z6]),(0,[z0,z1,z3,z4,z5,z239,z6]),(0,[z0,z1,z3,z4,z5,z6,z240])],[(0,[z41,z0,z1,z3,z28,z4,z6]),(0,[z0,z1,z3,z4,z5,z241,z6])],[(0,[z10,z0,z1,z3,z94,z5,z6]),(0,[z242,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z243,z4,z5,z6,z244]),(0,[z0,z1,z3,z4,z5,z6,z245])],[(0,[z0,z246,z1,z97,z4,z5,z6]),(0,[z0,z1,z247,z3,z4,z5,z6])],[(1,[z0,z1,z3,z4,z123,z6]),(0,[z0,z1,z248,z3,z4,z5,z6]),(0,[z249,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z250,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z251,z6]),(0,[z0,z252,z1,z3,z4,z5,z6]),(0,[z0,z27,z1,z35,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z253,z6])],[(1,[z92,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z254,z13,z5]),(0,[z255,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z256,z6]),(0,[z0,z1,z3,z4,z5,z151,z6])],[(1,[z31,z1,z3,z13,z5,z6]),(0,[z257,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z4,z5,z6,z258])]],
   [[(0,[z0,z1,z3,z4,z259,z5,z6]),(0,[z260,z0,z1,z3,z4,z5,z6]),(0,[z68,z0,z1,z3,z4,z5,z6]),(0,[z0,z261,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z262])],[(0,[z0,z263,z1,z3,z4,z5,z6]),(0,[z0,z1,z264,z3,z4,z5,z6]),(0,[z265,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z266,z3,z4,z5,z6]),(0,[z57,z0,z1,z3,z4,z49,z6]),(0,[z0,z1,z3,z267,z4,z5,z6]),(0,[z0,z1,z3,z4,z268,z5,z6]),(1,[z0,z246,z97,z4,z5,z6]),(1,[z0,z1,z269,z4,z5,z6])],[(0,[z0,z1,z3,z270,z4,z5,z6]),(0,[z98,z0,z1,z271,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z99,z6])],[(0,[z11,z1,z3,z4,z49,z5,z6]),(0,[z0,z1,z3,z272,z4,z5,z6]),(0,[z0,z1,z3,z189,z4,z5,z6])],[(0,[z0,z1,z273,z3,z4,z5,z6]),(0,[z274,z0,z1,z3,z4,z5,z6]),(0,[z202,z0,z1,z3,z189,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z275]),(0,[z40,z0,z1,z3,z28,z5,z6])],[(0,[z0,z1,z3,z4,z5,z276,z6]),(0,[z0,z277,z1,z3,z4,z5,z6]),(0,[z0,z1,z278,z3,z4,z5,z6]),(0,[z0,z1,z279,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z280,z6]),(0,[z0,z3,z189,z4,z281,z5,z6]),(0,[z282,z0,z1,z3,z4,z5,z6])],[(0,[z0,z283,z1,z243,z4,z5,z6]),(0,[z284,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z285,z4,z5,z6]),(0,[z93,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z286,z5,z6]),(0,[z0,z1,z3,z4,z5,z287,z6])],[(0,[z0,z288,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z289,z6]),(0,[z0,z1,z3,z4,z5,z6,z290]),(0,[z68,z0,z1,z4,z5,z73,z6]),(0,[z0,z1,z3,z74,z4,z5,z75])]],
   [[(0,[z0,z1,z3,z4,z5,z6,z291]),(0,[z0,z1,z3,z4,z292,z5,z6]),(0,[z0,z283,z1,z3,z4,z81,z6]),(0,[z0,z1,z243,z62,z4,z5,z6]),(1,[z0,z1,z4,z5,z143,z6])],[(0,[z0,z1,z3,z4,z281,z5,z6]),(0,[z43,z0,z1,z3,z4,z5,z67]),(0,[z0,z1,z3,z4,z5,z293,z6]),(0,[z0,z294,z1,z3,z4,z5,z6])],[(0,[z295,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z151,z144])],[(0,[z10,z119,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z296,z5,z6]),(0,[z297,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z136])],[(0,[z0,z1,z298,z3,z4,z5,z6]),(0,[z0,z246,z283,z3,z4,z5,z6]),(0,[z0,z1,z271,z4,z51,z5,z6]),(0,[z299,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z300,z3,z4,z5,z6]),(0,[z301,z0,z1,z3,z4,z5,z6]),(0,[z93,z0,z1,z3,z4,z169,z6]),(0,[z302,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z189,z13,z5,z6]),(0,[z0,z1,z3,z4,z214,z51,z5]),(0,[z0,z23,z1,z4,z5,z6,z244])],[(0,[z0,z1,z170,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z303,z6]),(0,[z0,z1,z3,z4,z5,z304,z6]),(0,[z0,z1,z64,z3,z4,z6,z136])]],
   [[(0,[z0,z1,z3,z4,z5,z6,z305]),(0,[z0,z1,z3,z4,z306,z5,z6])],[(0,[z0,z1,z307,z3,z4,z5,z6]),(0,[z308,z1,z3,z4,z5,z36,z6]),(0,[z0,z1,z3,z309,z4,z5,z6]),(0,[z0,z1,z165,z271,z4,z5,z6]),(0,[z0,z310,z1,z3,z4,z5,z6]),(0,[z0,z1,z311,z4,z5,z144,z6]),(0,[z0,z1,z3,z29,z5,z75,z6])],[(1,[z0,z252,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z312,z5,z6]),(0,[z313,z0,z1,z3,z4,z5,z6])],[(1,[z0,z1,z125,z3,z4,z6])],[(0,[z314,z0,z1,z3,z4,z5,z6]),(0,[z92,z0,z1,z3,z4,z13,z5]),(0,[z0,z1,z3,z4,z160,z36,z6])],[(0,[z0,z1,z315,z3,z4,z5,z6]),(0,[z0,z1,z62,z4,z5,z184,z6]),(0,[z0,z1,z3,z4,z5,z316,z6]),(0,[z0,z1,z3,z4,z5,z6,z317])],[(0,[z0,z1,z170,z4,z5,z73,z6]),(0,[z0,z1,z3,z318,z4,z5,z6]),(0,[z319,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z81,z6]),(0,[z0,z1,z3,z4,z5,z6,z320])],[(0,[z0,z170,z3,z83,z4,z5,z6]),(0,[z0,z1,z321,z3,z4,z5,z6]),(0,[z322,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z323]),(0,[z0,z1,z3,z4,z5,z6,z324]),(0,[z40,z0,z1,z62,z3,z4,z6]),(0,[z0,z325,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z326,z5,z6]),(1,[z0,z1,z64,z3,z4,z136])]],
   [[(1,[z60,z1,z3,z4,z5,z80]),(1,[z0,z23,z1,z4,z5,z244]),(0,[z0,z1,z3,z4,z5,z6,z327]),(0,[z0,z1,z64,z3,z28,z4,z6])],[(0,[z119,z11,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z328,z5,z6]),(0,[z0,z329,z1,z3,z4,z5,z6]),(0,[z68,z0,z1,z4,z211,z5,z6]),(0,[z0,z1,z3,z4,z330,z5,z6])],[(0,[z331,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z254,z5]),(0,[z0,z1,z62,z3,z4,z139,z6])],[(1,[z10,z88,z3,z4,z5,z6]),(0,[z43,z308,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z6,z332]),(0,[z333,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z73,z6]),(0,[z334,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z97,z4,z5,z6,z244]),(0,[z0,z1,z3,z4,z335,z5,z6]),(0,[z0,z1,z50,z3,z4,z5,z6]),(0,[z0,z23,z1,z62,z4,z5,z6])],[(0,[z0,z1,z3,z4,z336,z5,z6]),(0,[z0,z337,z1,z3,z4,z5,z6]),(0,[z0,z1,z338,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z339,z5,z6]),(1,[z0,z1,z340,z4,z5,z6]),(0,[z0,z1,z3,z74,z4,z5,z44]),(0,[z0,z1,z3,z341,z4,z5,z6])],[(0,[z0,z342,z1,z3,z4,z5,z6]),(0,[z0,z283,z243,z3,z4,z5,z6]),(0,[z0,z343,z1,z3,z4,z5,z6]),(0,[z344,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z345])]],
   [[(0,[z0,z1,z346,z3,z4,z5,z6]),(1,[z69,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z347,z4,z5,z6]),(0,[z0,z1,z348,z3,z4,z5,z6])],[(0,[z0,z349,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z350]),(0,[z0,z1,z3,z4,z5,z6,z351]),(0,[z0,z1,z3,z352,z4,z5,z6]),(0,[z353,z0,z1,z3,z4,z5,z6])],[],[(0,[z0,z1,z3,z4,z354,z5,z6]),(0,[z0,z124,z1,z3,z189,z5,z6]),(0,[z0,z66,z1,z35,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z6,z355])],[(0,[z0,z1,z3,z4,z356,z5,z6]),(0,[z0,z1,z3,z357,z4,z5,z6]),(0,[z358,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z145,z152,z6])],[(0,[z10,z0,z283,z3,z4,z5,z6]),(0,[z0,z1,z359,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z360])],[(0,[z0,z1,z3,z361,z4,z5,z6]),(0,[z0,z23,z1,z3,z4,z5,z244]),(0,[z0,z362,z1,z3,z4,z5,z6])],[(0,[z0,z252,z1,z3,z97,z4,z5]),(0,[z363,z0,z1,z3,z4,z5,z6]),(0,[z0,z364,z225,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z169,z6,z136]),(0,[z0,z1,z3,z365,z4,z5,z6])]],
   [[(0,[z0,z366,z1,z3,z4,z5,z6]),(0,[z367,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z368,z6])],[(0,[z57,z0,z1,z62,z3,z4,z6]),(0,[z369,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z370,z4,z5,z6]),(0,[z0,z1,z3,z4,z371,z5,z6])],[(0,[z0,z1,z3,z372,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z373,z6]),(0,[z0,z1,z3,z4,z374,z5,z6])],[(0,[z0,z1,z3,z375,z4,z5,z6]),(0,[z0,z1,z3,z4,z376,z5,z6]),(0,[z0,z1,z3,z4,z5,z377,z6]),(0,[z0,z1,z3,z28,z29,z5,z6])],[(1,[z0,z1,z3,z4,z115,z6]),(0,[z119,z0,z11,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z378,z6]),(0,[z0,z1,z3,z4,z5,z6,z379]),(0,[z0,z380,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z381,z4,z5,z6]),(0,[z0,z1,z3,z4,z211,z5,z6])],[(1,[z0,z1,z3,z153,z5,z6]),(0,[z57,z0,z1,z3,z4,z6,z136]),(0,[z0,z1,z3,z4,z5,z382,z6]),(0,[z0,z124,z1,z3,z4,z5,z104]),(0,[z0,z1,z3,z383,z4,z5,z6]),(0,[z0,z1,z3,z4,z6,z16,z44])],[(0,[z0,z1,z12,z3,z4,z5,z6]),(0,[z0,z1,z384,z3,z4,z5,z6]),(0,[z385,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z386,z6]),(0,[z0,z1,z3,z271,z4,z5,z6]),(0,[z0,z1,z3,z4,z145,z5,z152])]],
   [[(0,[z0,z1,z3,z387,z4,z5,z6]),(0,[z0,z66,z3,z4,z5,z67,z6]),(0,[z0,z23,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z388,z4,z5,z6]),(0,[z0,z1,z3,z4,z389,z5,z6])],[(0,[z0,z1,z3,z4,z5,z390,z6]),(0,[z0,z1,z3,z4,z5,z391,z6]),(0,[z392,z0,z1,z3,z4,z5,z6])],[(0,[z0,z23,z1,z170,z4,z5,z6]),(0,[z0,z393,z1,z3,z4,z5,z6])],[(0,[z0,z124,z1,z387,z4,z5,z6]),(1,[z0,z364,z3,z4,z139,z6]),(0,[z0,z1,z3,z4,z5,z394,z6]),(0,[z0,z1,z3,z4,z5,z395,z6])],[(1,[z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z396,z13,z6]),(0,[z0,z1,z35,z243,z4,z5,z6]),(0,[z0,z1,z3,z397,z4,z5,z6]),(0,[z398,z0,z1,z3,z4,z5,z6])],[(0,[z10,z0,z1,z375,z4,z5,z6]),(0,[z399,z0,z1,z3,z4,z5,z6]),(0,[z400,z0,z1,z3,z4,z5,z6]),(0,[z1,z3,z25,z4,z13,z5,z6]),(0,[z0,z283,z1,z3,z4,z401,z6]),(0,[z402,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z403,z3,z4,z5,z6]),(1,[z43,z0,z1,z3,z5,z44]),(0,[z0,z1,z3,z404,z4,z5,z6])],[(0,[z0,z405,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z406,z5,z6]),(0,[z0,z1,z3,z4,z29,z5,z6])],[(0,[z40,z57,z0,z1,z3,z4,z6]),(0,[z57,z0,z1,z3,z28,z4,z6]),(0,[z0,z1,z3,z4,z407,z5,z6])]],
   [[(0,[z0,z408,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z409,z6])],[(0,[z0,z1,z3,z4,z5,z410,z6]),(1,[z202,z0,z3,z281,z5,z6]),(1,[z0,z1,z131,z4,z5,z6])],[(0,[z10,z0,z1,z3,z4,z5,z116]),(0,[z68,z0,z1,z97,z4,z5,z6]),(0,[z0,z1,z3,z411,z4,z5,z6])],[(0,[z0,z1,z412,z3,z4,z5,z6]),(0,[z0,z413,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z414,z4,z5,z6]),(0,[z0,z1,z3,z4,z415,z5,z6]),(0,[z0,z364,z1,z269,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z416,z6]),(0,[z0,z417,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z418,z4,z5,z6])],[(0,[z419,z0,z1,z3,z4,z5,z6]),(0,[z40,z0,z1,z3,z5,z75,z6])],[(0,[z420,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z421,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z422]),(0,[z0,z423,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z424,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z425,z6]),(0,[z40,z93,z0,z1,z3,z4,z6]),(0,[z426,z0,z1,z3,z5,z6,z136])],[(0,[z10,z0,z88,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z427]),(0,[z0,z1,z3,z4,z428,z5,z6]),(0,[z0,z1,z3,z4,z5,z429,z6]),(0,[z0,z1,z3,z4,z430,z5,z6]),(0,[z0,z364,z1,z431,z4,z5,z6]),(0,[z0,z27,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z5,z6,z432,z136])]],
   [[(0,[z0,z1,z3,z4,z182,z5,z6]),(0,[z0,z1,z3,z4,z5,z433,z6])],[(0,[z10,z202,z0,z3,z4,z5,z6]),(0,[z91,z0,z1,z3,z4,z5,z6]),(0,[z0,z23,z1,z3,z4,z5,z80]),(0,[z0,z124,z1,z412,z4,z5,z6]),(0,[z0,z1,z62,z3,z4,z5,z6])],[(1,[z0,z1,z3,z4,z5,z434]),(0,[z11,z1,z88,z3,z4,z5,z6]),(0,[z435,z0,z1,z3,z4,z5,z6]),(0,[z308,z0,z1,z194,z4,z5,z6]),(0,[z0,z27,z1,z3,z4,z5,z134]),(0,[z436,z0,z1,z3,z4,z5,z6])],[(0,[z91,z0,z1,z170,z4,z5,z6]),(0,[z0,z1,z437,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z67,z80]),(1,[z0,z1,z3,z4,z401,z6]),(0,[z0,z438,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z439,z6])],[(0,[z0,z1,z3,z4,z440,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z441])],[(0,[z0,z1,z3,z4,z5,z442,z6])],[(0,[z0,z1,z3,z443,z4,z5,z6]),(0,[z0,z444,z1,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z245,z44])],[(0,[z0,z1,z3,z4,z5,z6,z445]),(1,[z0,z1,z431,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z36,z6,z209]),(0,[z446,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z62,z3,z4,z169,z6]),(0,[z0,z364,z1,z3,z4,z139,z6]),(0,[z0,z1,z447,z3,z4,z5,z6]),(0,[z0,z1,z62,z4,z5,z73,z6])],[(0,[z0,z1,z3,z4,z448,z5,z6]),(0,[z0,z1,z170,z97,z4,z5,z6]),(0,[z0,z23,z1,z4,z211,z5,z6])],[(0,[z202,z119,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z449,z4,z5,z6]),(0,[z0,z1,z3,z4,z49,z5,z6]),(0,[z0,z1,z3,z4,z5,z75,z6])],[(0,[z0,z450,z1,z3,z4,z5,z6]),(0,[z43,z0,z1,z35,z3,z4,z5])],[(0,[z68,z91,z0,z1,z4,z5,z6]),(0,[z451,z0,z1,z3,z4,z5,z6])],[(0,[z452,z0,z1,z3,z4,z5,z6]),(0,[z98,z0,z1,z3,z4,z5,z156]),(1,[z14,z0,z1,z4,z5,z6]),(0,[z0,z453,z1,z3,z4,z5,z6]),(0,[z0,z124,z1,z3,z4,z5,z454]),(0,[z0,z1,z3,z4,z5,z455,z6]),(1,[z0,z89,z1,z3,z4,z5]),(0,[z456,z0,z1,z3,z4,z5,z6])],[(0,[z119,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z97,z4,z5,z6]),(0,[z0,z1,z457,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z458])],[(0,[z0,z1,z3,z4,z5,z459,z6])]],
   [[(0,[z0,z460,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z461,z4,z5,z6]),(0,[z462,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z217,z6]),(0,[z0,z1,z3,z4,z5,z463,z6]),(0,[z0,z1,z3,z4,z5,z464,z6])],[(1,[z98,z1,z170,z4,z5,z6]),(0,[z0,z1,z3,z4,z49,z169,z6]),(0,[z0,z223,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z160,z5,z6]),(0,[z465,z0,z1,z3,z4,z5,z6]),(0,[z0,z225,z1,z3,z4,z139,z6]),(0,[z0,z1,z3,z4,z5,z466,z6])],[(0,[z0,z1,z3,z4,z5,z467,z6]),(0,[z468,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z469,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z36,z6]),(0,[z0,z1,z3,z4,z470,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z471]),(0,[z202,z0,z1,z3,z281,z5,z6]),(0,[z0,z1,z311,z3,z4,z5,z6])],[(1,[z0,z1,z3,z94,z5,z6]),(0,[z41,z0,z1,z3,z4,z145,z6]),(0,[z0,z1,z3,z4,z472,z5,z6]),(0,[z0,z473,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z474,z6])],[(0,[z0,z475,z1,z3,z4,z5,z6]),(0,[z476,z0,z1,z3,z4,z5,z6]),(0,[z0,z477,z1,z3,z4,z5,z6]),(0,[z0,z1,z478,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z479])],[(0,[z480,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z481,z5,z6]),(0,[z0,z1,z3,z4,z5,z36,z134]),(0,[z0,z1,z62,z3,z4,z184,z6]),(0,[z0,z1,z4,z211,z5,z184,z6]),(0,[z0,z1,z3,z29,z5,z144,z6])],[(0,[z10,z1,z3,z4,z49,z5,z6]),(1,[z482,z1,z3,z25,z5,z6]),(0,[z0,z483,z1,z3,z4,z5,z6]),(0,[z484,z0,z1,z3,z4,z5,z6])]],
   [[(1,[z91,z1,z24,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z485]),(0,[z0,z1,z3,z4,z5,z486,z6]),(0,[z487,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z488,z6]),(0,[z489,z0,z1,z3,z4,z5,z6]),(0,[z490,z0,z1,z3,z4,z5,z6]),(0,[z43,z0,z1,z3,z29,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z491]),(0,[z0,z492,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z25,z281,z5,z6]),(0,[z0,z1,z3,z4,z5,z67,z36]),(1,[z0,z1,z3,z4,z241,z6])],[(0,[z493,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z494,z5,z6]),(0,[z0,z1,z495,z3,z4,z5,z6]),(0,[z0,z1,z3,z496,z4,z5,z6]),(0,[z0,z1,z3,z497,z4,z5,z6]),(0,[z0,z498,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z499])],[(0,[z91,z98,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z500,z4,z5,z6]),(0,[z0,z501,z1,z3,z4,z5,z6]),(0,[z0,z1,z62,z271,z4,z5,z6]),(0,[z0,z23,z1,z3,z74,z4,z5])],[(0,[z0,z1,z3,z24,z4,z5,z6]),(0,[z0,z1,z3,z4,z39,z5,z6]),(0,[z0,z1,z3,z4,z139,z5,z6]),(1,[z0,z1,z4,z5,z6,z245]),(1,[z0,z1,z3,z4,z6,z16])],[(0,[z502,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z503,z3,z4,z5,z6]),(0,[z308,z60,z1,z3,z4,z5,z6]),(0,[z0,z246,z1,z243,z4,z5,z6]),(0,[z93,z0,z1,z3,z4,z184,z6]),(0,[z0,z1,z3,z4,z5,z504,z6])],[(0,[z10,z0,z1,z12,z4,z5,z6]),(0,[z10,z0,z27,z3,z4,z5,z6]),(0,[z0,z1,z243,z3,z4,z5,z6]),(1,[z0,z283,z243,z4,z5,z6]),(0,[z0,z505,z1,z3,z4,z5,z6]),(0,[z468,z1,z3,z4,z5,z169,z6]),(0,[z506,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z271,z4,z211,z5,z6])]],
   [[(0,[z0,z1,z3,z138,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z507,z6]),(0,[z0,z1,z3,z4,z508,z5,z6])],[(0,[z0,z1,z509,z3,z4,z5,z6]),(0,[z0,z1,z243,z170,z4,z5,z6]),(1,[z0,z1,z3,z461,z4,z5]),(0,[z0,z1,z3,z4,z5,z6,z510])],[(0,[z10,z0,z3,z4,z5,z67,z6]),(0,[z0,z1,z3,z4,z5,z6,z156]),(0,[z93,z0,z1,z4,z211,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z511]),(0,[z0,z1,z3,z512,z4,z5,z6])],[(0,[z482,z0,z1,z3,z25,z5,z6]),(1,[z41,z1,z3,z4,z49,z6]),(0,[z0,z1,z3,z4,z5,z513,z6]),(0,[z0,z1,z3,z514,z4,z5,z6]),(0,[z0,z1,z515,z3,z4,z5,z6]),(0,[z0,z1,z3,z516,z4,z5,z6]),(0,[z0,z1,z3,z4,z517,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z518])],[(1,[z0,z288,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z67,z6,z134]),(1,[z0,z105,z1,z4,z5,z6])],[(0,[z482,z1,z3,z25,z4,z5,z6]),(0,[z0,z519,z1,z3,z4,z5,z6]),(0,[z0,z246,z3,z97,z4,z5,z6]),(0,[z0,z364,z3,z4,z139,z5,z6]),(0,[z0,z1,z3,z4,z520,z5,z6]),(0,[z0,z1,z3,z74,z4,z5,z67]),(0,[z521,z0,z1,z3,z4,z5,z6]),(0,[z522,z0,z1,z3,z4,z5,z6])],[(0,[z0,z3,z4,z523,z13,z5,z6]),(0,[z0,z1,z3,z4,z524,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z525])],[(0,[z0,z1,z1,z3,z4,z5,z6])]],
   [[(0,[z93,z41,z0,z1,z3,z4,z6]),(0,[z0,z66,z1,z3,z4,z5,z134]),(1,[z0,z1,z3,z5,z6,z432])],[(0,[z0,z1,z526,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z427,z6]),(0,[z0,z1,z3,z527,z4,z5,z6]),(0,[z0,z283,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z528,z6]),(1,[z68,z0,z1,z51,z5,z6]),(0,[z0,z529,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z145,z152])],[(0,[z0,z1,z3,z4,z5,z530,z6]),(1,[z40,z0,z1,z3,z144,z6]),(0,[z0,z1,z3,z4,z152,z6,z136])],[(0,[z531,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z532,z5,z6]),(0,[z0,z27,z1,z340,z4,z5,z6]),(0,[z533,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z534,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z535]),(0,[z0,z536,z1,z3,z4,z5,z6]),(0,[z0,z537,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z538]),(0,[z0,z1,z3,z539,z4,z5,z6])],[(0,[z540,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z541,z5,z6]),(0,[z0,z1,z3,z4,z5,z542,z6])],[(0,[z0,z543,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z544,z6]),(0,[z0,z1,z545,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z145,z5,z136])],[(0,[z0,z1,z3,z4,z5,z546,z6]),(0,[z0,z1,z3,z4,z58,z169,z6]),(0,[z0,z1,z3,z4,z139,z58,z6]),(0,[z0,z364,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z547]),(0,[z0,z1,z3,z548,z4,z5,z6])]],
   [[(0,[z0,z3,z4,z5,z99,z6,z80])],[(0,[z0,z549,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z550,z6]),(0,[z0,z551,z1,z3,z4,z5,z6])],[(0,[z167,z0,z1,z3,z24,z4,z6]),(1,[z0,z3,z4,z523,z5,z6]),(0,[z0,z124,z1,z3,z281,z5,z6]),(0,[z0,z1,z3,z4,z552,z5,z6]),(0,[z0,z1,z3,z4,z5,z553,z6])],[(0,[z0,z1,z3,z4,z554,z5,z6]),(0,[z0,z1,z3,z4,z5,z555,z6]),(0,[z0,z1,z3,z4,z556,z5,z6]),(0,[z0,z1,z557,z3,z4,z5,z6]),(1,[z0,z1,z3,z74,z5,z75]),(0,[z0,z1,z558,z3,z4,z5,z6]),(0,[z0,z1,z64,z3,z4,z145,z6])],[(0,[z0,z1,z3,z559,z4,z5,z6]),(0,[z308,z0,z1,z3,z74,z4,z5]),(0,[z0,z560,z1,z3,z4,z5,z6])],[(0,[z69,z0,z1,z3,z4,z5,z6]),(0,[z41,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z52,z3,z4,z5]),(0,[z0,z1,z561,z3,z4,z5,z6])],[(0,[z10,z0,z3,z189,z4,z5,z6]),(0,[z482,z0,z1,z3,z4,z5,z6]),(0,[z0,z562,z1,z3,z4,z5,z6]),(0,[z0,z364,z1,z3,z4,z169,z6]),(0,[z0,z1,z563,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z564,z5,z6]),(0,[z0,z1,z3,z565,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z566,z6])]],
   [[(0,[z0,z1,z243,z4,z211,z5,z6]),(1,[z0,z124,z3,z189,z5,z6]),(0,[z0,z225,z1,z3,z4,z5,z6]),(0,[z0,z27,z1,z3,z4,z5,z67]),(1,[z0,z1,z62,z4,z184,z6])],[(0,[z0,z567,z1,z3,z4,z5,z6]),(0,[z568,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z569,z4,z5,z6]),(0,[z0,z1,z570,z3,z4,z5,z6]),(1,[z0,z27,z3,z4,z5,z134]),(0,[z0,z1,z3,z4,z5,z6,z134]),(0,[z0,z1,z3,z4,z5,z571,z6])],[(0,[z572,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z461,z97,z4,z5]),(0,[z0,z1,z243,z271,z4,z5,z6]),(0,[z40,z0,z1,z3,z4,z139,z6]),(0,[z573,z0,z1,z3,z4,z5,z6]),(0,[z0,z23,z1,z35,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z574,z6]),(1,[z0,z1,z575,z4,z5,z6]),(0,[z0,z1,z62,z97,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z576,z6])],[(0,[z0,z1,z3,z577,z4,z5,z6]),(0,[z0,z578,z1,z3,z4,z5,z6]),(0,[z0,z579,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z580])],[(0,[z0,z1,z575,z3,z4,z5,z6]),(0,[z0,z1,z3,z28,z4,z139,z6]),(0,[z0,z1,z3,z4,z214,z5,z6]),(0,[z0,z1,z3,z4,z5,z581,z6]),(0,[z0,z1,z3,z4,z5,z6,z582]),(0,[z0,z1,z64,z3,z74,z4,z5])],[(0,[z10,z0,z3,z97,z4,z5,z6]),(0,[z57,z11,z1,z3,z4,z5,z6]),(0,[z0,z246,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z583,z5,z6]),(1,[z308,z1,z3,z4,z5,z36]),(0,[z0,z225,z1,z3,z4,z169,z6])]],
   [[(0,[z584,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z35,z3,z74,z4,z5])],[(0,[z482,z0,z1,z3,z13,z5,z6]),(0,[z0,z243,z3,z97,z4,z5,z6]),(0,[z68,z0,z1,z165,z4,z5,z6]),(0,[z0,z1,z3,z4,z585,z5,z6])],[(0,[z0,z586,z1,z3,z4,z5,z6]),(0,[z587,z0,z1,z3,z4,z5,z6]),(0,[z0,z588,z1,z3,z4,z5,z6]),(0,[z0,z1,z589,z3,z4,z5,z6]),(1,[z468,z1,z3,z4,z5,z6]),(0,[z590,z0,z1,z3,z4,z5,z6]),(0,[z40,z0,z1,z3,z5,z144,z6])],[(0,[z0,z591,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z592,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z593,z6]),(0,[z40,z0,z1,z3,z4,z29,z6])],[(0,[z0,z1,z3,z4,z5,z6,z434]),(0,[z0,z1,z3,z4,z5,z594,z6]),(0,[z0,z1,z3,z4,z5,z6,z595])],[(0,[z0,z1,z3,z4,z5,z596,z6]),(0,[z0,z597,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z598,z5,z6])],[(0,[z0,z599,z1,z3,z4,z5,z6]),(1,[z322,z0,z1,z3,z4,z6]),(0,[z60,z0,z1,z3,z74,z4,z5]),(0,[z600,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z601]),(0,[z0,z1,z602,z3,z4,z5,z6])],[(0,[z0,z1,z603,z3,z4,z5,z6]),(0,[z41,z0,z1,z3,z4,z58,z6]),(0,[z604,z0,z1,z3,z4,z5,z6]),(0,[z0,z27,z1,z131,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z605,z6])]],
   [[(0,[z606,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z607,z5,z6]),(0,[z0,z1,z3,z194,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z608,z6]),(1,[z0,z1,z311,z4,z5,z6]),(0,[z609,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z115,z6]),(0,[z0,z1,z4,z211,z5,z73,z6])],[(0,[z41,z57,z1,z3,z4,z5,z6]),(0,[z0,z1,z610,z3,z4,z5,z6]),(0,[z0,z1,z611,z3,z4,z5,z6])],[(0,[z0,z612,z1,z3,z4,z5,z6]),(0,[z613,z0,z1,z3,z4,z5,z6]),(0,[z308,z0,z1,z3,z4,z5,z6]),(0,[z0,z614,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z615]),(0,[z0,z616,z1,z3,z4,z5,z6])],[(0,[z0,z3,z4,z139,z5,z169,z6]),(0,[z0,z1,z52,z3,z4,z5,z144])],[(0,[z1,z3,z4,z5,z386,z169,z6]),(0,[z617,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z35,z3,z4,z5,z244]),(0,[z0,z1,z4,z5,z73,z6,z244])],[(0,[z0,z1,z3,z618,z4,z5,z6]),(0,[z0,z619,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z104]),(0,[z0,z23,z1,z271,z4,z5,z6])],[(1,[z0,z1,z375,z4,z5,z6]),(0,[z308,z0,z1,z575,z4,z5,z6]),(0,[z0,z1,z620,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z621,z5,z6]),(0,[z0,z1,z3,z4,z5,z622,z6]),(0,[z0,z1,z3,z4,z5,z144,z6]),(0,[z0,z1,z623,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z5,z6]),(0,[z0,z1,z3,z624,z4,z5,z6]),(0,[z43,z0,z1,z3,z4,z5,z134]),(0,[z0,z23,z66,z1,z3,z4,z5]),(0,[z0,z1,z271,z4,z5,z73,z6]),(0,[z625,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z626,z3,z4,z5,z6])],[(0,[z10,z0,z1,z3,z153,z5,z6]),(0,[z0,z1,z627,z3,z4,z5,z6]),(0,[z0,z628,z1,z3,z4,z5,z6])],[(0,[z0,z629,z1,z3,z4,z5,z6]),(0,[z57,z0,z1,z3,z4,z145,z6]),(1,[z0,z1,z3,z4,z6,z209]),(0,[z0,z124,z1,z3,z4,z630,z6])],[(0,[z631,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z387,z4,z5,z6]),(0,[z0,z632,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z633,z5,z6]),(0,[z0,z1,z3,z4,z634,z5,z6]),(0,[z0,z1,z3,z4,z635,z5,z6])],[(0,[z636,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z116]),(0,[z0,z1,z3,z4,z637,z5,z6]),(0,[z0,z1,z3,z4,z396,z5,z6]),(0,[z0,z27,z3,z4,z5,z6,z134]),(0,[z0,z1,z3,z4,z5,z6,z638]),(0,[z0,z1,z64,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z639,z5,z6])],[(0,[z0,z640,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z641,z4,z5,z6]),(1,[z1,z3,z4,z5,z386,z6])],[(0,[z0,z1,z3,z4,z5,z169,z6]),(0,[z0,z1,z3,z4,z51,z5,z6]),(0,[z0,z1,z3,z642,z4,z5,z6]),(0,[z0,z1,z35,z3,z4,z5,z6])]],
   [[(0,[z0,z11,z1,z3,z4,z5,z6]),(1,[z0,z3,z83,z4,z5,z6]),(1,[z0,z1,z3,z4,z396,z6]),(0,[z0,z27,z66,z3,z4,z5,z6])],[(0,[z119,z0,z283,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z630,z5,z6]),(0,[z43,z0,z1,z3,z4,z145,z5])],[(0,[z60,z1,z3,z4,z5,z6,z80]),(0,[z0,z1,z97,z4,z211,z5,z6]),(0,[z0,z1,z3,z4,z643,z5,z6]),(0,[z202,z0,z3,z4,z281,z5,z6]),(0,[z0,z1,z3,z4,z644,z5,z6]),(0,[z0,z645,z1,z3,z4,z5,z6])],[(0,[z646,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z647,z6]),(0,[z0,z23,z1,z3,z4,z5,z36]),(0,[z648,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z649,z4,z5,z6])],[(0,[z0,z1,z24,z4,z5,z73,z6]),(0,[z308,z0,z1,z3,z4,z5,z80]),(0,[z0,z1,z97,z271,z4,z5,z6]),(0,[z0,z650,z1,z3,z4,z5,z6]),(0,[z651,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z652,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z258])],[(0,[z60,z0,z1,z3,z4,z5,z6]),(0,[z68,z0,z1,z243,z4,z5,z6]),(1,[z0,z1,z50,z3,z4,z6]),(0,[z0,z1,z165,z3,z271,z5,z6]),(0,[z653,z0,z1,z3,z4,z5,z6]),(0,[z0,z654,z1,z3,z4,z5,z6]),(0,[z0,z1,z135,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z655,z6]),(0,[z31,z1,z3,z4,z13,z5,z6]),(1,[z57,z1,z3,z4,z58,z6]),(0,[z0,z1,z3,z269,z4,z5,z6]),(0,[z0,z1,z35,z4,z5,z73,z6]),(0,[z0,z656,z1,z3,z4,z5,z6]),(0,[z426,z0,z1,z3,z4,z5,z6])],[(0,[z0,z657,z1,z3,z4,z5,z6]),(0,[z91,z0,z1,z271,z4,z5,z6]),(0,[z0,z1,z3,z4,z658,z5,z6]),(0,[z31,z0,z1,z3,z25,z5,z6]),(0,[z0,z1,z3,z4,z5,z401,z6]),(1,[z0,z1,z165,z271,z5,z6]),(0,[z0,z1,z3,z4,z659,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z432])]],
   [[(0,[z0,z660,z1,z3,z4,z5,z6]),(0,[z661,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z662,z5,z6]),(0,[z663,z0,z1,z3,z4,z5,z6]),(0,[z0,z89,z1,z3,z4,z51,z5]),(0,[z0,z1,z3,z4,z5,z664,z6]),(0,[z40,z0,z1,z3,z4,z144,z6]),(0,[z0,z1,z4,z5,z6,z258,z136]),(0,[z0,z1,z3,z4,z5,z665,z6])],[(0,[z0,z1,z3,z13,z281,z5,z6]),(0,[z14,z0,z1,z4,z13,z5,z6]),(1,[z0,z1,z412,z4,z5,z6]),(0,[z40,z0,z1,z3,z4,z5,z6])],[(0,[z10,z0,z1,z3,z4,z123,z6]),(0,[z0,z666,z1,z3,z4,z5,z6]),(0,[z667,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z668,z3,z4,z5,z6]),(1,[z426,z0,z1,z3,z5,z6])],[(0,[z0,z1,z3,z4,z5,z669,z6]),(0,[z0,z283,z1,z97,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z454,z6]),(0,[z670,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z671,z5,z6]),(0,[z0,z1,z3,z28,z4,z144,z6]),(0,[z0,z1,z3,z4,z672,z5,z6])],[(0,[z98,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z673,z6]),(0,[z0,z23,z1,z3,z4,z5,z73]),(0,[z0,z1,z3,z28,z4,z5,z6]),(0,[z0,z674,z1,z3,z4,z5,z6])],[(0,[z10,z0,z1,z3,z4,z5,z434]),(0,[z31,z482,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z523,z5,z6]),(0,[z0,z1,z3,z4,z675,z5,z6]),(0,[z0,z1,z3,z4,z5,z143,z6])],[(0,[z98,z0,z1,z170,z4,z5,z6]),(0,[z0,z1,z340,z3,z4,z5,z6])],[(0,[z68,z0,z1,z3,z271,z5,z6]),(0,[z0,z1,z64,z3,z4,z5,z152])]],
   [[(0,[z0,z1,z243,z24,z4,z5,z6]),(0,[z0,z1,z35,z3,z4,z5,z80]),(0,[z0,z225,z3,z4,z5,z169,z6]),(0,[z40,z0,z1,z3,z4,z169,z6]),(0,[z0,z66,z1,z3,z4,z5,z6]),(0,[z0,z27,z1,z3,z4,z241,z6])],[(0,[z0,z1,z3,z4,z5,z6,z676]),(0,[z0,z1,z677,z3,z4,z5,z6]),(0,[z68,z0,z1,z62,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z678]),(0,[z40,z0,z1,z3,z4,z152,z6])],[(0,[z0,z679,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z44])],[(0,[z0,z1,z3,z4,z139,z49,z6]),(0,[z0,z1,z3,z4,z5,z680,z6]),(0,[z0,z1,z3,z28,z4,z169,z6]),(0,[z68,z0,z23,z1,z4,z5,z6]),(0,[z0,z1,z3,z4,z681,z5,z6]),(0,[z43,z0,z1,z3,z4,z5,z75])],[(0,[z0,z1,z3,z682,z4,z5,z6]),(0,[z0,z1,z3,z683,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z217,z6]),(0,[z0,z1,z3,z4,z5,z6,z684]),(0,[z0,z1,z3,z28,z4,z152,z6])],[(1,[z0,z1,z3,z4,z5,z454]),(0,[z0,z1,z3,z685,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z686])],[(0,[z0,z1,z3,z4,z5,z6,z687]),(0,[z0,z688,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z689,z6]),(0,[z60,z0,z1,z3,z4,z5,z80]),(0,[z1,z3,z4,z5,z36,z6,z80])],[(0,[z0,z690,z1,z3,z4,z5,z6]),(0,[z98,z0,z1,z3,z4,z5,z427]),(0,[z0,z288,z170,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z630,z6]),(0,[z0,z1,z3,z4,z5,z6,z244]),(1,[z0,z1,z35,z4,z5,z73]),(0,[z691,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z692,z0,z1,z3,z4,z5,z6]),(0,[z693,z0,z1,z3,z4,z5,z6]),(0,[z0,z694,z1,z3,z4,z5,z6])],[(0,[z0,z1,z695,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z696,z5,z6]),(0,[z0,z1,z3,z4,z697,z5,z6]),(0,[z0,z1,z3,z698,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z699])],[(0,[z31,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z5,z75,z6,z44]),(0,[z0,z1,z3,z74,z4,z145,z5])],[(0,[z119,z0,z88,z3,z4,z5,z6]),(0,[z57,z0,z1,z3,z4,z5,z6]),(0,[z308,z0,z1,z3,z4,z5,z36]),(0,[z0,z124,z3,z189,z4,z5,z6]),(0,[z0,z1,z165,z3,z4,z5,z6]),(0,[z0,z1,z700,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z701,z5,z6])],[(0,[z0,z223,z3,z4,z5,z6,z80]),(0,[z0,z1,z3,z4,z702,z5,z6])],[(0,[z0,z703,z1,z3,z4,z5,z6]),(0,[z202,z0,z1,z3,z4,z5,z6])],[(0,[z704,z0,z1,z3,z4,z5,z6]),(1,[z167,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z705,z5,z6]),(0,[z0,z1,z3,z4,z706,z5,z6])],[(0,[z322,z0,z1,z3,z4,z13,z6]),(0,[z0,z1,z3,z4,z254,z5,z6]),(0,[z0,z1,z431,z3,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z3,z4,z707,z6])],[(0,[z0,z708,z3,z4,z5,z6]),(0,[z0,z1,z709,z3,z4,z6]),(0,[z1,z3,z4,z5,z6,z710]),(0,[z0,z1,z711,z4,z5,z6]),(0,[z0,z1,z3,z4,z712,z6])],[(0,[z0,z1,z3,z4,z713,z6]),(0,[z0,z1,z387,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z116]),(0,[z0,z1,z3,z4,z714,z6]),(0,[z0,z252,z1,z24,z4,z5]),(0,[z468,z1,z3,z4,z58,z6]),(0,[z0,z124,z3,z189,z217,z6]),(0,[z0,z1,z35,z4,z635,z5])],[(0,[z0,z1,z3,z138,z4,z6])],[(0,[z0,z1,z3,z715,z5,z6]),(0,[z1,z3,z4,z5,z386,z6]),(0,[z0,z1,z3,z4,z716,z5]),(0,[z0,z1,z35,z131,z4,z5])],[(0,[z0,z1,z3,z4,z6,z717]),(0,[z426,z57,z0,z1,z3,z6]),(0,[z41,z1,z3,z4,z6,z479]),(0,[z0,z1,z3,z4,z5,z718]),(0,[z719,z1,z3,z4,z5,z6])],[(0,[z0,z1,z720,z4,z5,z6]),(0,[z0,z1,z3,z721,z5,z6]),(0,[z0,z1,z3,z4,z722,z6]),(0,[z0,z1,z723,z4,z5,z6]),(0,[z60,z492,z1,z3,z4,z5]),(0,[z0,z1,z50,z271,z4,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z724]),(0,[z0,z283,z725,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z726])],[(0,[z0,z1,z3,z4,z5,z727]),(0,[z98,z1,z728,z4,z5,z6]),(0,[z0,z1,z35,z4,z5,z467]),(0,[z0,z23,z1,z469,z4,z5])],[(0,[z0,z1,z3,z4,z160,z6]),(0,[z0,z1,z3,z4,z145,z391]),(0,[z1,z3,z4,z729,z58,z6]),(0,[z0,z1,z3,z730,z5,z6]),(0,[z68,z0,z89,z1,z4,z5])],[(0,[z0,z731,z3,z4,z5,z6]),(0,[z0,z543,z3,z4,z169,z6]),(0,[z1,z3,z4,z732,z5,z6]),(0,[z0,z733,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z734,z6]),(0,[z0,z4,z39,z523,z5,z6]),(0,[z0,z735,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z736]),(0,[z0,z1,z737,z3,z4,z6]),(0,[z68,z0,z1,z214,z51,z5]),(0,[z0,z1,z50,z3,z4,z6]),(0,[z0,z1,z3,z4,z738,z6])],[(0,[z0,z288,z97,z4,z5,z6]),(0,[z0,z1,z739,z4,z5,z6]),(0,[z0,z246,z725,z4,z5,z6]),(0,[z0,z1,z62,z54,z4,z6]),(0,[z0,z1,z4,z6,z16,z245])],[(0,[z0,z1,z3,z4,z740,z6]),(0,[z0,z27,z3,z4,z241,z134]),(0,[z0,z741,z1,z4,z5,z6])],[(0,[z10,z88,z12,z4,z5,z6]),(0,[z0,z1,z742,z4,z5,z6]),(0,[z0,z1,z743,z4,z5,z6]),(0,[z41,z0,z1,z135,z4,z6]),(0,[z0,z1,z3,z744,z5,z6]),(0,[z0,z1,z3,z4,z6,z745])]],
   [[(0,[z0,z1,z3,z4,z746,z6]),(0,[z402,z1,z3,z25,z5,z6]),(0,[z0,z1,z747,z3,z4,z5]),(0,[z0,z1,z64,z3,z4,z439]),(1,[z0,z1,z3,z5,z748])],[(0,[z0,z1,z3,z4,z749,z6]),(0,[z0,z27,z563,z3,z4,z5]),(0,[z426,z0,z1,z3,z5,z6]),(0,[z40,z0,z1,z3,z151,z144])],[(0,[z0,z1,z3,z4,z750,z6]),(0,[z0,z1,z575,z4,z5,z36])],[(0,[z0,z1,z3,z4,z751,z6]),(0,[z0,z1,z752,z4,z5,z6])],[(0,[z41,z1,z3,z4,z148,z6]),(0,[z0,z1,z35,z4,z5,z753]),(0,[z0,z1,z4,z5,z73,z753])],[(0,[z0,z288,z12,z4,z5,z6])],[(0,[z0,z1,z3,z4,z145,z155])],[(0,[z0,z1,z3,z4,z754,z6]),(0,[z0,z755,z1,z3,z4,z6])]],
   [[(0,[z426,z0,z1,z3,z169,z6]),(0,[z756,z0,z1,z3,z4,z6])],[(0,[z1,z3,z4,z49,z115,z6]),(0,[z0,z1,z757,z4,z5,z6]),(0,[z91,z1,z138,z24,z4,z6]),(0,[z40,z0,z1,z3,z406,z6]),(0,[z0,z1,z3,z74,z470,z5]),(0,[z0,z1,z387,z4,z5,z104]),(0,[z0,z1,z758,z4,z5,z6]),(0,[z426,z0,z1,z3,z152,z6])],[(0,[z0,z759,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z760,z6]),(0,[z0,z1,z3,z4,z761,z5]),(0,[z0,z1,z3,z5,z6,z762])],[(0,[z0,z1,z375,z4,z5,z116]),(0,[z0,z1,z3,z763,z4,z5]),(0,[z322,z0,z1,z4,z39,z6]),(0,[z0,z3,z4,z764,z5,z6]),(0,[z0,z1,z3,z4,z765,z6]),(0,[z0,z1,z3,z4,z214,z5]),(0,[z0,z1,z125,z3,z75,z6]),(0,[z0,z1,z3,z4,z726,z136])],[(0,[z0,z1,z3,z4,z766,z6]),(0,[z0,z3,z4,z767,z5,z6]),(0,[z0,z1,z3,z4,z5,z454])],[(0,[z0,z1,z3,z768,z5,z6]),(0,[z98,z170,z83,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z769]),(0,[z0,z1,z4,z5,z6,z770])],[(0,[z0,z1,z375,z94,z5,z6]),(0,[z0,z1,z3,z771,z5,z6]),(0,[z0,z1,z3,z4,z772,z5]),(0,[z0,z1,z3,z4,z630,z6]),(0,[z0,z1,z387,z4,z217,z6]),(0,[z0,z1,z35,z4,z5,z73]),(1,[z40,z0,z1,z52,z3]),(0,[z0,z1,z4,z5,z143,z151]),(0,[z0,z1,z773,z4,z5,z6])],[(0,[z0,z616,z3,z4,z169,z6]),(0,[z43,z0,z105,z1,z4,z5])]],
   [[(0,[z0,z1,z3,z4,z5,z774]),(0,[z0,z775,z3,z4,z5,z6]),(0,[z14,z0,z1,z4,z396,z6]),(0,[z0,z1,z3,z4,z776,z6]),(0,[z0,z1,z62,z418,z4,z6])],[(0,[z0,z1,z12,z4,z115,z6]),(0,[z0,z1,z3,z4,z5,z777]),(0,[z0,z27,z3,z4,z5,z778])],[(0,[z0,z1,z3,z153,z123,z6]),(0,[z0,z1,z779,z4,z5,z6]),(0,[z60,z3,z4,z5,z99,z80]),(0,[z0,z223,z3,z4,z5,z134]),(0,[z0,z1,z243,z4,z81,z6])],[(0,[z0,z1,z3,z94,z5,z116]),(0,[z0,z1,z3,z28,z6,z686])],[(0,[z0,z1,z780,z4,z5,z6]),(0,[z0,z37,z3,z4,z139,z6]),(0,[z0,z1,z3,z4,z182,z6]),(0,[z0,z1,z4,z211,z239,z6])],[(0,[z167,z0,z1,z3,z4,z6]),(0,[z0,z252,z1,z131,z4,z5]),(0,[z590,z0,z23,z1,z4,z5]),(1,[z0,z1,z3,z781,z6]),(0,[z43,z0,z1,z5,z245,z44])],[(0,[z0,z1,z782,z4,z5,z6]),(0,[z0,z1,z62,z4,z530,z6])],[(0,[z0,z783,z1,z3,z4,z6]),(0,[z0,z695,z97,z4,z5,z6]),(0,[z0,z1,z3,z4,z784,z6]),(0,[z0,z3,z725,z4,z5,z6]),(0,[z0,z1,z412,z4,z5,z104])]],
   [[(0,[z0,z1,z12,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z785]),(0,[z322,z0,z3,z4,z523,z6]),(0,[z0,z252,z1,z35,z4,z5]),(1,[z0,z1,z786,z5,z6]),(0,[z68,z0,z1,z182,z51,z6])],[(0,[z468,z1,z3,z4,z6,z136]),(0,[z0,z1,z3,z4,z5,z787]),(0,[z40,z0,z1,z52,z3,z4]),(0,[z0,z1,z4,z788,z5,z6])],[(0,[z202,z0,z3,z94,z5,z6]),(0,[z0,z1,z3,z4,z5,z789]),(0,[z43,z0,z1,z3,z108,z5]),(0,[z0,z1,z698,z271,z5,z6]),(0,[z68,z0,z1,z376,z5,z6]),(0,[z0,z1,z3,z28,z781,z6]),(0,[z0,z1,z3,z4,z145,z726])],[(0,[z31,z1,z3,z13,z5,z6]),(0,[z0,z1,z790,z3,z4,z5]),(0,[z0,z1,z340,z4,z110,z6]),(0,[z0,z1,z3,z28,z29,z6])],[(0,[z0,z1,z3,z791,z5,z6]),(0,[z0,z1,z3,z792,z5,z6]),(0,[z793,z0,z1,z4,z5,z6]),(0,[z0,z1,z794,z3,z4,z5]),(0,[z0,z1,z795,z3,z4,z6])],[(0,[z0,z223,z3,z4,z5,z434]),(0,[z0,z246,z97,z4,z5,z6])],[(0,[z1,z3,z4,z49,z655,z6]),(0,[z0,z796,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z797,z6]),(0,[z0,z1,z3,z4,z5,z798]),(0,[z0,z1,z3,z29,z6,z133])],[(0,[z0,z1,z3,z4,z799,z5]),(0,[z0,z3,z4,z5,z800,z6]),(0,[z0,z801,z1,z4,z5,z6]),(0,[z93,z0,z1,z4,z339,z6])]],
   [[(0,[z1,z170,z728,z4,z5,z6]),(0,[z0,z1,z3,z4,z802,z6]),(0,[z0,z1,z35,z285,z4,z5]),(0,[z0,z1,z5,z6,z258,z432])],[(0,[z0,z803,z3,z4,z5,z6]),(0,[z0,z1,z135,z4,z139,z6]),(0,[z0,z23,z1,z4,z5,z491]),(0,[z0,z1,z3,z4,z6,z726])],[(0,[z0,z1,z804,z4,z5,z6]),(0,[z0,z805,z3,z4,z5,z6]),(0,[z468,z1,z3,z28,z4,z6])],[(0,[z43,z0,z1,z125,z3,z44])],[(0,[z0,z1,z806,z3,z4,z5])],[(0,[z0,z1,z3,z807,z5,z6]),(0,[z0,z66,z3,z4,z5,z67])],[(0,[z0,z1,z3,z4,z123,z434]),(0,[z0,z1,z808,z4,z5,z6]),(0,[z0,z3,z4,z139,z809,z6]),(0,[z0,z810,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z811,z6]),(0,[z0,z1,z3,z4,z5,z812]),(0,[z0,z1,z3,z4,z813,z6]),(0,[z0,z1,z50,z3,z4,z214])]],
   [[(0,[z0,z1,z3,z4,z814,z6]),(0,[z119,z3,z4,z87,z5,z6]),(0,[z815,z0,z1,z3,z4,z6]),(0,[z0,z1,z816,z4,z5,z6]),(0,[z0,z1,z3,z4,z217,z454]),(0,[z0,z1,z64,z3,z4,z262]),(0,[z0,z1,z311,z28,z4,z6])],[(0,[z0,z3,z4,z5,z67,z434]),(0,[z0,z1,z817,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z818]),(0,[z0,z1,z3,z4,z819,z6]),(0,[z0,z1,z820,z4,z5,z6]),(0,[z0,z1,z3,z4,z821,z6])],[(0,[z0,z1,z822,z4,z5,z6]),(0,[z69,z14,z0,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z823])],[(0,[z0,z1,z4,z5,z6,z824]),(0,[z0,z225,z3,z4,z809,z6]),(0,[z0,z1,z3,z4,z6,z825])],[(0,[z0,z1,z3,z4,z5,z826]),(0,[z0,z1,z3,z4,z5,z827]),(0,[z0,z223,z3,z4,z828,z6]),(0,[z0,z1,z3,z4,z829,z6]),(0,[z0,z1,z3,z4,z5,z830])],[(0,[z119,z0,z131,z4,z5,z6]),(0,[z0,z1,z3,z831,z4,z5]),(0,[z0,z1,z832,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z833])],[(0,[z0,z3,z4,z5,z99,z6]),(0,[z0,z1,z3,z4,z5,z834]),(0,[z0,z252,z1,z3,z4,z5]),(0,[z1,z835,z3,z4,z5,z6])],[(0,[z0,z1,z836,z4,z5,z6]),(0,[z468,z1,z3,z4,z49,z6]),(0,[z0,z1,z837,z4,z5,z6])]],
   [[(0,[z0,z3,z4,z838,z5,z6]),(0,[z0,z1,z3,z4,z149,z136]),(0,[z0,z1,z3,z4,z839,z6])],[(0,[z0,z1,z3,z4,z5,z840]),(0,[z0,z1,z3,z4,z841,z5]),(0,[z842,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z843,z5,z6]),(0,[z0,z1,z3,z4,z844,z6])],[(0,[z0,z1,z3,z4,z81,z6]),(0,[z0,z725,z97,z4,z5,z6]),(0,[z0,z124,z3,z730,z5,z6]),(0,[z0,z1,z3,z4,z110,z6]),(0,[z0,z845,z1,z4,z5,z6]),(0,[z43,z0,z1,z125,z3,z6])],[(0,[z0,z1,z3,z4,z846,z6]),(0,[z0,z1,z64,z3,z4,z136])],[(1,[z1,z3,z4,z729,z6]),(0,[z847,z1,z3,z4,z5,z6]),(0,[z0,z1,z4,z211,z6,z327]),(0,[z0,z23,z1,z4,z5,z244])],[(0,[z0,z1,z848,z4,z5,z6]),(0,[z0,z1,z3,z28,z208,z6])],[(0,[z0,z1,z4,z5,z6,z849]),(0,[z0,z1,z3,z4,z729,z6]),(0,[z0,z850,z3,z4,z5,z6]),(0,[z60,z223,z3,z4,z5,z80]),(0,[z0,z124,z387,z189,z5,z6]),(0,[z0,z1,z3,z4,z851,z6]),(0,[z0,z3,z4,z5,z852,z6])],[(0,[z0,z1,z3,z28,z109,z6]),(0,[z0,z1,z131,z4,z110,z6]),(0,[z0,z1,z4,z5,z6,z853]),(0,[z0,z23,z1,z4,z5,z547]),(0,[z0,z1,z854,z4,z5,z6])]],
   [[(0,[z0,z1,z12,z94,z5,z6]),(0,[z855,z0,z1,z4,z5,z6]),(0,[z0,z1,z3,z856,z4,z6]),(0,[z43,z0,z105,z1,z5,z44])],[(0,[z10,z100,z3,z4,z5,z6]),(0,[z522,z1,z3,z4,z5,z36]),(0,[z0,z1,z4,z5,z857,z6])],[(0,[z0,z1,z858,z4,z5,z6]),(0,[z40,z0,z1,z3,z439,z6]),(0,[z0,z1,z3,z4,z5,z151]),(0,[z0,z1,z3,z5,z75,z55])],[(0,[z0,z1,z3,z4,z859,z6]),(0,[z0,z1,z3,z4,z6,z860]),(0,[z0,z1,z3,z4,z5,z861]),(0,[z0,z862,z1,z3,z4,z5]),(0,[z0,z863,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z156]),(0,[z0,z3,z4,z5,z6,z864]),(0,[z0,z223,z858,z4,z5,z6]),(0,[z0,z1,z431,z4,z139,z6])],[(0,[z31,z14,z1,z13,z5,z6]),(0,[z0,z1,z3,z4,z5,z865]),(0,[z0,z310,z3,z4,z169,z6]),(0,[z866,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z867]),(0,[z0,z1,z3,z5,z75,z748])],[(0,[z93,z0,z1,z565,z4,z6]),(0,[z0,z23,z1,z4,z5,z18]),(0,[z0,z868,z1,z3,z4,z5]),(0,[z0,z1,z869,z4,z5,z6]),(0,[z0,z1,z3,z29,z781,z6])]],
   [[],[(0,[z870,z88,z3,z4,z5,z6]),(0,[z299,z1,z3,z4,z5,z80]),(0,[z0,z3,z4,z730,z5,z6]),(0,[z0,z1,z871,z4,z5,z6]),(0,[z0,z1,z62,z4,z872,z6])],[(0,[z10,z88,z3,z4,z123,z6]),(0,[z0,z1,z3,z4,z5,z873]),(0,[z0,z656,z3,z4,z5,z67]),(0,[z0,z1,z3,z4,z874,z6]),(0,[z40,z0,z1,z52,z3,z5])],[(0,[z0,z1,z3,z153,z115,z6]),(0,[z0,z1,z4,z786,z5,z6]),(0,[z426,z0,z1,z5,z6,z258]),(0,[z0,z1,z3,z4,z152,z726])],[(0,[z0,z1,z875,z4,z5,z6]),(0,[z0,z246,z252,z97,z4,z5]),(0,[z0,z124,z412,z189,z5,z6]),(0,[z40,z0,z1,z3,z455,z6])],[(0,[z10,z88,z3,z4,z5,z434]),(0,[z308,z1,z3,z4,z160,z36]),(0,[z0,z1,z3,z4,z876,z6]),(0,[z0,z1,z3,z4,z877,z6])],[(0,[z0,z1,z3,z4,z5,z878]),(0,[z0,z1,z3,z4,z879,z6]),(0,[z353,z1,z3,z4,z5,z80]),(0,[z0,z1,z64,z3,z4,z726])],[(0,[z0,z1,z3,z4,z880,z6]),(0,[z0,z1,z881,z4,z5,z6]),(0,[z0,z1,z3,z4,z882,z6]),(0,[z0,z1,z883,z4,z5,z6])]],
   [[(0,[z0,z1,z884,z4,z5,z6]),(0,[z0,z1,z3,z4,z145,z416]),(0,[z0,z885,z3,z4,z5,z6]),(0,[z0,z1,z135,z4,z5,z6])],[(0,[z0,z1,z4,z396,z39,z6]),(0,[z0,z1,z3,z5,z886,z6])],[(0,[z0,z1,z3,z153,z5,z6]),(0,[z0,z1,z3,z887,z5,z6]),(0,[z0,z1,z194,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z888]),(1,[z0,z1,z4,z872,z6]),(0,[z43,z0,z1,z3,z17,z5])],[(0,[z0,z1,z3,z4,z5,z889]),(0,[z31,z1,z3,z890,z5,z6]),(0,[z31,z322,z1,z3,z13,z6]),(0,[z57,z1,z3,z4,z729,z6]),(0,[z0,z325,z97,z4,z5,z6]),(0,[z0,z1,z3,z4,z891,z6]),(0,[z0,z1,z3,z4,z892,z5]),(0,[z0,z1,z311,z4,z5,z151]),(0,[z893,z0,z3,z4,z5,z6])],[(0,[z0,z1,z4,z5,z73,z535]),(0,[z0,z1,z894,z4,z5,z6])],[(0,[z0,z1,z3,z895,z4,z6]),(0,[z896,z0,z1,z3,z4,z5])],[(0,[z0,z1,z3,z4,z897,z6]),(0,[z191,z1,z170,z4,z5,z6]),(0,[z426,z0,z1,z135,z5,z6])],[(0,[z0,z3,z189,z94,z5,z6]),(0,[z0,z1,z3,z898,z5,z6]),(0,[z0,z1,z3,z4,z5,z899]),(0,[z0,z1,z3,z4,z900,z6]),(0,[z0,z364,z3,z4,z139,z6]),(0,[z0,z1,z135,z4,z169,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z901]),(0,[z0,z902,z1,z3,z4,z5]),(0,[z0,z124,z3,z189,z5,z454])],[(0,[z0,z252,z1,z4,z211,z5]),(0,[z43,z0,z1,z3,z5,z44])],[(0,[z0,z223,z3,z4,z5,z6]),(0,[z119,z3,z230,z4,z5,z6]),(0,[z0,z124,z3,z189,z630,z6]),(0,[z0,z225,z3,z4,z169,z6]),(0,[z0,z1,z3,z4,z5,z903]),(0,[z0,z1,z904,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z905]),(0,[z0,z3,z4,z396,z523,z6]),(0,[z0,z1,z4,z906,z5,z6]),(0,[z0,z1,z907,z4,z5,z6]),(0,[z93,z0,z1,z4,z211,z6])],[(0,[z908,z0,z1,z3,z4,z5]),(0,[z0,z560,z243,z4,z5,z6])],[(0,[z31,z69,z3,z13,z5,z6]),(0,[z202,z0,z3,z281,z5,z6]),(0,[z0,z1,z4,z5,z909,z6])],[(0,[z0,z1,z4,z254,z39,z5]),(0,[z0,z1,z3,z4,z910,z6]),(0,[z0,z364,z3,z4,z809,z6]),(0,[z0,z911,z1,z4,z5,z6]),(0,[z0,z1,z3,z781,z144,z6])],[(0,[z0,z1,z3,z4,z115,z434]),(0,[z11,z3,z4,z5,z507,z6]),(0,[z0,z1,z912,z4,z5,z6]),(0,[z468,z1,z62,z3,z4,z6]),(0,[z0,z3,z4,z5,z67,z778])]],
   [[(0,[z0,z1,z3,z153,z5,z434]),(0,[z313,z1,z3,z4,z49,z6])],[(0,[z10,z870,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z913,z6]),(0,[z167,z91,z1,z24,z4,z6]),(0,[z98,z1,z170,z4,z5,z156]),(0,[z0,z1,z3,z4,z5,z914])],[(0,[z0,z223,z3,z4,z915,z6])],[(0,[z0,z1,z3,z4,z123,z6]),(0,[z0,z1,z3,z4,z5,z916]),(0,[z917,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z918,z6]),(0,[z919,z0,z1,z3,z4,z6])],[(0,[z0,z1,z3,z4,z5,z920]),(1,[z0,z3,z730,z5,z6]),(0,[z0,z1,z3,z4,z5,z921])],[(0,[z92,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z922]),(0,[z923,z1,z3,z4,z5,z6]),(0,[z0,z283,z243,z4,z81,z6]),(0,[z468,z225,z3,z4,z169,z6]),(0,[z0,z924,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z434]),(0,[z925,z1,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z258]),(0,[z926,z1,z3,z4,z5,z6])],[(0,[z927,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z401,z6]),(0,[z0,z1,z928,z4,z5,z6]),(0,[z0,z364,z269,z4,z139,z6]),(0,[z0,z1,z3,z4,z5,z748])]],
   [[(0,[z0,z1,z3,z4,z5,z929]),(0,[z0,z1,z3,z4,z5,z930]),(0,[z0,z288,z243,z4,z5,z6]),(0,[z0,z3,z4,z254,z523,z5]),(0,[z0,z1,z269,z4,z5,z6]),(0,[z0,z1,z931,z4,z5,z6])],[(0,[z0,z3,z4,z5,z67,z22]),(0,[z0,z1,z3,z4,z932,z6])],[(0,[z0,z1,z3,z4,z5,z933]),(0,[z0,z3,z4,z809,z5,z6]),(0,[z0,z364,z431,z4,z139,z6]),(0,[z0,z23,z1,z4,z5,z157])],[(0,[z0,z283,z12,z4,z5,z6]),(0,[z0,z1,z431,z4,z5,z6]),(0,[z1,z3,z4,z5,z934,z6]),(0,[z0,z1,z4,z935,z5,z6])],[(0,[z0,z1,z936,z4,z5,z6]),(0,[z0,z342,z3,z189,z5,z6]),(0,[z57,z1,z3,z4,z179,z6]),(0,[z40,z0,z1,z52,z3,z144])],[(0,[z0,z1,z937,z4,z5,z6]),(0,[z0,z1,z938,z4,z5,z6]),(0,[z0,z1,z3,z4,z939,z5]),(0,[z69,z0,z3,z4,z254,z5]),(0,[z940,z1,z3,z4,z5,z6]),(0,[z0,z1,z786,z51,z5,z6])],[(0,[z941,z0,z1,z3,z4,z6]),(0,[z1,z3,z4,z5,z942,z6]),(0,[z0,z1,z3,z4,z5,z943]),(0,[z0,z1,z3,z786,z5,z6])],[(0,[z0,z1,z3,z944,z5,z6]),(0,[z10,z597,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z945]),(0,[z0,z1,z4,z5,z143,z6])]],
   [[(0,[z1,z3,z890,z13,z5,z6]),(0,[z14,z92,z0,z1,z4,z5]),(0,[z0,z1,z3,z4,z630,z104]),(0,[z93,z468,z1,z3,z4,z6])],[(0,[z0,z1,z946,z4,z5,z6]),(0,[z0,z3,z4,z809,z169,z6]),(0,[z0,z89,z1,z50,z3,z4]),(1,[z43,z0,z1,z125,z3])],[(0,[z0,z1,z3,z947,z4,z6]),(0,[z0,z1,z138,z4,z73,z6]),(0,[z0,z948,z3,z4,z5,z6]),(0,[z0,z3,z949,z4,z5,z6]),(0,[z0,z1,z950,z4,z5,z6]),(0,[z0,z1,z431,z4,z169,z6])],[(0,[z0,z1,z3,z4,z5,z951]),(0,[z14,z322,z0,z1,z4,z6]),(0,[z0,z1,z3,z4,z952,z6]),(0,[z308,z1,z3,z4,z36,z209]),(0,[z0,z1,z387,z4,z5,z454])],[(0,[z0,z953,z1,z3,z4,z6]),(0,[z1,z3,z4,z890,z5,z6]),(0,[z0,z954,z3,z4,z5,z6]),(0,[z0,z252,z1,z271,z4,z5]),(1,[z0,z1,z4,z5,z753])],[(0,[z0,z1,z3,z4,z5,z955]),(0,[z0,z223,z956,z4,z5,z6]),(0,[z0,z1,z3,z4,z828,z6]),(0,[z0,z1,z387,z4,z630,z6])],[(0,[z0,z957,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z6,z958]),(0,[z0,z588,z1,z4,z211,z6]),(0,[z0,z1,z3,z4,z959,z6]),(0,[z68,z0,z1,z786,z5,z6]),(0,[z43,z0,z1,z3,z5,z748])]],
   [[(0,[z0,z960,z3,z4,z5,z6]),(0,[z0,z1,z961,z4,z5,z6]),(0,[z0,z105,z1,z125,z4,z6])],[(0,[z0,z1,z962,z4,z5,z6]),(0,[z1,z870,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z963,z6])],[(0,[z0,z1,z964,z4,z5,z6]),(0,[z0,z1,z4,z5,z965,z6]),(0,[z0,z1,z125,z3,z4,z6])],[(0,[z10,z88,z3,z4,z115,z6]),(0,[z0,z1,z3,z966,z4,z6]),(0,[z0,z967,z1,z4,z5,z6]),(0,[z0,z1,z3,z4,z809,z6])],[(0,[z10,z88,z3,z153,z5,z6]),(0,[z0,z1,z3,z4,z968,z6]),(0,[z91,z1,z24,z4,z5,z6]),(0,[z0,z1,z969,z3,z4,z6]),(0,[z0,z3,z4,z5,z6,z970])],[(0,[z0,z1,z971,z4,z5,z6]),(0,[z972,z0,z1,z3,z4,z5]),(0,[z0,z973,z3,z4,z5,z6]),(0,[z0,z1,z3,z974,z5,z6]),(0,[z68,z0,z1,z440,z5,z6]),(0,[z0,z537,z3,z4,z139,z6]),(0,[z0,z1,z62,z4,z306,z6])],[(0,[z0,z1,z3,z975,z5,z6]),(0,[z91,z1,z728,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z976]),(0,[z57,z0,z1,z135,z4,z6]),(0,[z0,z1,z62,z4,z524,z6])],[(0,[z60,z1,z3,z4,z5,z80]),(0,[z1,z3,z4,z5,z977,z6]),(0,[z0,z27,z3,z4,z110,z134]),(1,[z0,z1,z3,z4,z726]),(0,[z426,z0,z1,z64,z3,z136])]],
   [[(0,[z0,z1,z12,z4,z5,z116])],[(0,[z0,z1,z3,z4,z254,z5]),(0,[z0,z1,z412,z4,z5,z454]),(0,[z0,z1,z4,z5,z6,z245]),(0,[z40,z0,z1,z311,z4,z6]),(0,[z0,z1,z3,z4,z6,z16])],[(0,[z10,z88,z3,z4,z5,z6]),(0,[z0,z1,z3,z978,z5,z6]),(0,[z93,z0,z1,z4,z672,z6])],[(0,[z0,z1,z3,z94,z123,z6]),(0,[z0,z979,z1,z3,z4,z5]),(0,[z0,z1,z412,z4,z630,z6]),(0,[z0,z1,z980,z3,z4,z6]),(0,[z981,z0,z1,z3,z5,z6]),(0,[z0,z1,z4,z5,z6,z982])],[(0,[z0,z1,z340,z4,z5,z6]),(0,[z0,z3,z730,z281,z5,z6]),(0,[z0,z1,z135,z5,z6,z432])],[(0,[z0,z1,z3,z4,z5,z983])],[(0,[z10,z0,z131,z4,z5,z6]),(0,[z0,z1,z3,z4,z984,z6]),(0,[z68,z0,z252,z1,z4,z5])],[(0,[z69,z0,z3,z4,z5,z6]),(0,[z41,z1,z3,z4,z49,z6]),(0,[z0,z1,z3,z4,z985,z5]),(0,[z0,z1,z986,z4,z5,z6])]],
   [[(0,[z0,z288,z3,z4,z5,z6]),(0,[z0,z105,z1,z4,z5,z6]),(0,[z0,z89,z1,z3,z4,z182]),(0,[z0,z1,z3,z74,z5,z542]),(0,[z0,z1,z64,z135,z4,z136])],[(0,[z693,z1,z24,z4,z5,z6]),(0,[z69,z322,z0,z3,z4,z6]),(0,[z0,z1,z3,z4,z987,z6]),(0,[z0,z1,z125,z3,z74,z4])],[(0,[z0,z1,z3,z4,z988,z6]),(0,[z0,z1,z4,z5,z6,z989]),(0,[z0,z3,z4,z5,z778,z134]),(0,[z0,z1,z3,z4,z182,z214]),(0,[z0,z1,z990,z4,z5,z6])],[(0,[z0,z1,z3,z4,z991,z6])],[(0,[z0,z277,z3,z4,z139,z6]),(0,[z0,z1,z3,z5,z6,z432])],[(0,[z0,z1,z992,z4,z5,z6])],[(0,[z0,z1,z3,z4,z993,z6]),(0,[z0,z1,z3,z4,z994,z6]),(0,[z40,z0,z1,z3,z144,z6])],[(0,[z0,z1,z3,z4,z630,z454]),(0,[z0,z1,z271,z5,z605,z6])]],
   [[(0,[z0,z1,z4,z995,z5,z6]),(0,[z0,z996,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z977,z80]),(0,[z0,z1,z997,z4,z5,z6]),(0,[z0,z1,z3,z4,z152,z518])],[(0,[z0,z1,z3,z4,z998,z6]),(1,[z1,z3,z890,z5,z6]),(0,[z0,z1,z3,z4,z5,z999]),(0,[z0,z1,z4,z5,z1000,z6]),(0,[z426,z0,z1,z64,z3,z5])],[(0,[z0,z283,z243,z4,z401,z6]),(0,[z68,z0,z1,z50,z51,z6]),(1,[z426,z0,z1,z64,z3])],[(0,[z31,z92,z1,z3,z13,z5]),(0,[z0,z1,z3,z890,z5,z6]),(0,[z69,z0,z3,z189,z5,z6]),(0,[z0,z223,z3,z4,z5,z67]),(0,[z1001,z1,z3,z4,z5,z6]),(0,[z0,z1,z4,z872,z5,z6])],[(0,[z0,z1,z3,z4,z115,z6]),(0,[z0,z246,z461,z97,z4,z5]),(0,[z0,z1,z3,z1002,z5,z6]),(0,[z0,z1,z3,z4,z5,z778])],[(0,[z0,z1,z1003,z4,z5,z6]),(0,[z0,z1,z3,z4,z1004,z6]),(0,[z0,z1,z52,z3,z28,z4])],[(0,[z0,z1,z3,z4,z5,z1005]),(0,[z0,z3,z4,z523,z5,z6]),(0,[z31,z3,z523,z13,z5,z6])],[(0,[z0,z1,z3,z4,z6,z1006]),(0,[z43,z0,z1,z3,z376,z5]),(0,[z0,z1,z3,z74,z5,z75])]],
   [[(0,[z0,z1,z4,z1007,z5,z6]),(0,[z119,z0,z252,z3,z4,z5]),(0,[z119,z3,z4,z5,z394,z6]),(0,[z31,z1,z39,z13,z5,z6]),(0,[z0,z1,z315,z3,z4,z136]),(0,[z0,z1,z3,z4,z5,z1008])],[(0,[z0,z1,z3,z4,z5,z1009]),(0,[z0,z1,z52,z3,z4,z5])],[(0,[z14,z0,z1,z4,z254,z5]),(0,[z0,z252,z1,z62,z4,z5]),(0,[z0,z1,z3,z4,z1010,z6]),(1,[z0,z3,z4,z809,z6]),(0,[z0,z1011,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z1012,z5,z6]),(0,[z98,z1,z4,z706,z5,z6]),(0,[z0,z1,z1013,z4,z5,z6])],[(0,[z0,z1,z62,z4,z184,z6])],[(0,[z0,z12,z97,z4,z5,z6]),(0,[z0,z1,z3,z4,z1014,z6]),(0,[z0,z1015,z3,z4,z5,z6]),(0,[z426,z41,z0,z1,z3,z6]),(0,[z308,z1,z194,z4,z5,z36]),(0,[z1,z3,z4,z5,z36,z977]),(0,[z0,z1,z3,z28,z644,z6]),(0,[z0,z1,z3,z4,z1016,z6]),(0,[z0,z1,z52,z3,z29,z5])],[(0,[z0,z1,z3,z4,z1017,z6]),(0,[z0,z1,z1018,z4,z5,z6])],[(0,[z468,z1,z3,z4,z115,z6]),(0,[z0,z1,z575,z4,z5,z6]),(0,[z0,z1,z1019,z4,z5,z6]),(0,[z1020,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1021,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z1022]),(0,[z0,z1,z131,z4,z5,z6]),(0,[z0,z1,z3,z4,z872,z6]),(0,[z0,z1,z52,z4,z5,z143])],[(0,[z0,z1,z3,z4,z1023,z5]),(0,[z0,z23,z1,z131,z4,z5]),(0,[z68,z0,z1,z681,z5,z6]),(0,[z0,z1,z3,z5,z781,z6])],[(0,[z10,z88,z3,z94,z5,z6]),(0,[z1024,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z5,z6,z1025]),(0,[z40,z0,z1,z311,z144,z6])],[(0,[z0,z1,z3,z4,z915,z6]),(0,[z600,z1,z3,z4,z5,z36]),(0,[z40,z0,z1,z52,z3,z6])],[(0,[z0,z1,z1026,z4,z5,z6]),(0,[z0,z690,z97,z4,z5,z6]),(0,[z322,z0,z1,z3,z4,z254]),(0,[z0,z1,z62,z4,z216,z6]),(0,[z1027,z1,z3,z4,z5,z6])],[(0,[z98,z288,z170,z4,z5,z6]),(0,[z0,z1,z3,z4,z1028,z6]),(0,[z0,z1029,z3,z4,z5,z6]),(0,[z0,z1030,z1,z3,z4,z5]),(0,[z0,z1,z4,z5,z753,z244])],[(0,[z468,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z427]),(0,[z0,z1031,z3,z4,z5,z6])],[(0,[z69,z0,z3,z94,z5,z6]),(0,[z68,z0,z1,z696,z5,z6]),(0,[z1,z728,z24,z4,z5,z6]),(0,[z60,z1,z3,z4,z5,z977]),(0,[z0,z1032,z1,z3,z4,z5])]],
   [[(0,[z0,z1,z170,z4,z5,z427]),(0,[z385,z1,z3,z13,z5,z6]),(0,[z69,z0,z3,z4,z396,z6]),(0,[z1033,z0,z1,z3,z4,z6]),(0,[z0,z1,z4,z872,z184,z6])],[(0,[z0,z1,z3,z4,z1034,z6]),(0,[z57,z1,z3,z4,z115,z6]),(0,[z0,z1,z3,z1035,z5,z6])],[(0,[z0,z1,z3,z1036,z5,z6]),(0,[z322,z0,z1,z3,z4,z6]),(0,[z0,z1,z340,z4,z241,z6]),(0,[z0,z1,z1037,z3,z4,z5]),(0,[z0,z1,z4,z5,z6,z753]),(0,[z40,z0,z1,z143,z144,z6])],[(0,[z0,z1,z3,z4,z5,z1038]),(0,[z0,z1,z3,z4,z1039,z6]),(0,[z31,z1,z3,z254,z13,z5]),(0,[z0,z1,z62,z4,z237,z6]),(0,[z426,z0,z1,z64,z3,z4])],[(0,[z0,z1,z3,z4,z1040,z6]),(0,[z0,z1,z3,z4,z5,z1041]),(0,[z43,z0,z1,z575,z4,z5]),(0,[z202,z0,z3,z730,z5,z6]),(0,[z0,z1,z311,z4,z5,z6])],[(0,[z0,z1,z375,z153,z5,z6]),(0,[z32,z1,z24,z4,z5,z6]),(0,[z0,z1,z138,z97,z4,z6]),(0,[z0,z243,z725,z4,z5,z6]),(0,[z0,z1,z52,z311,z4,z5])],[(0,[z0,z1042,z3,z4,z5,z6]),(0,[z1043,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z1044,z5,z6])],[(0,[z68,z0,z1,z4,z5,z427]),(0,[z0,z89,z1,z271,z4,z5]),(0,[z43,z0,z1,z3,z5,z262])]],
   [[(0,[z0,z1,z3,z4,z5,z1045]),(0,[z0,z1,z575,z4,z5,z80]),(0,[z0,z23,z1,z4,z5,z753])],[(0,[z1046,z0,z1,z3,z5,z6]),(0,[z0,z23,z1,z534,z4,z5]),(0,[z0,z1,z271,z5,z6,z678]),(0,[z0,z105,z1,z4,z6,z16])],[(0,[z0,z1,z3,z153,z5,z116]),(0,[z14,z0,z4,z523,z5,z6]),(0,[z0,z1,z3,z4,z5,z104]),(0,[z0,z1,z4,z5,z73,z601]),(0,[z1047,z0,z1,z3,z4,z6])],[(0,[z0,z1,z375,z4,z5,z6]),(1,[z0,z3,z4,z5,z778]),(0,[z93,z0,z1,z4,z872,z6]),(0,[z40,z0,z1,z3,z781,z6])],[(0,[z0,z1,z3,z94,z115,z6]),(0,[z14,z0,z1,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1048]),(0,[z0,z89,z1,z3,z4,z5]),(0,[z0,z105,z1,z74,z4,z5])],[(0,[z0,z1049,z3,z4,z5,z6]),(0,[z0,z1,z1050,z4,z5,z6]),(0,[z0,z1,z725,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1051]),(0,[z0,z1,z3,z5,z6,z748])],[(0,[z0,z1,z3,z4,z396,z254]),(0,[z0,z1,z3,z4,z6,z209]),(0,[z0,z1,z956,z4,z5,z6]),(0,[z0,z1052,z3,z4,z5,z6]),(0,[z0,z1,z4,z1053,z5,z6])],[(0,[z0,z1,z3,z4,z6,z1054]),(0,[z0,z1,z97,z4,z81,z6]),(0,[z0,z1,z3,z4,z217,z6])]],
   [[(0,[z98,z1,z170,z4,z5,z6]),(0,[z0,z252,z1,z4,z5,z244]),(0,[z0,z1,z3,z4,z5,z1055]),(0,[z40,z0,z1,z3,z681,z6]),(0,[z43,z0,z1,z125,z3,z4])],[(0,[z0,z1,z3,z1056,z4,z6]),(0,[z0,z1,z3,z5,z6,z1057]),(0,[z0,z1,z3,z4,z5,z1058]),(0,[z1059,z1,z3,z4,z5,z6]),(0,[z0,z1,z4,z211,z872,z6])],[(0,[z10,z273,z3,z4,z5,z6]),(0,[z0,z1060,z3,z4,z5,z6])],[(0,[z0,z1,z3,z94,z5,z6]),(0,[z0,z1,z3,z4,z5,z1061]),(0,[z1,z3,z4,z49,z729,z6])],[(0,[z10,z122,z3,z4,z5,z6]),(0,[z0,z3,z83,z4,z5,z6]),(0,[z0,z1,z3,z4,z396,z6]),(0,[z92,z322,z0,z1,z3,z4]),(0,[z1062,z0,z1,z3,z5,z6]),(0,[z0,z1063,z1,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1064]),(0,[z0,z1,z3,z4,z5,z1065]),(0,[z0,z1,z1066,z4,z5,z6]),(0,[z0,z1,z4,z1067,z5,z6])],[(0,[z0,z1,z375,z4,z123,z6]),(0,[z0,z1,z271,z554,z5,z6]),(0,[z482,z1,z3,z25,z5,z6]),(0,[z0,z1,z1068,z4,z5,z6]),(0,[z1069,z0,z3,z4,z5,z6])],[(0,[z0,z1,z35,z4,z5,z459]),(0,[z0,z1,z3,z4,z781,z6])]],
   [[(0,[z0,z1,z3,z1070,z5,z6])],[(0,[z0,z1,z375,z4,z5,z434]),(0,[z0,z1,z271,z4,z5,z427]),(0,[z1071,z0,z1,z4,z5,z6]),(0,[z0,z1,z3,z4,z241,z6]),(0,[z0,z1,z3,z4,z6,z1072])],[(0,[z0,z1,z3,z4,z1073,z6]),(0,[z57,z1,z3,z4,z58,z6]),(0,[z0,z1,z1074,z4,z5,z6]),(0,[z0,z1,z3,z1075,z4,z6]),(0,[z0,z1,z3,z4,z5,z753])],[(0,[z0,z1,z3,z4,z123,z116]),(0,[z98,z1,z170,z4,z5,z427]),(0,[z0,z1,z3,z4,z1076,z6]),(0,[z0,z1,z1077,z4,z5,z6]),(0,[z0,z1,z165,z271,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1078])],[(0,[z1079,z0,z1,z3,z5,z6]),(0,[z0,z1080,z1,z3,z4,z5]),(0,[z1,z3,z25,z890,z5,z6]),(0,[z0,z1,z412,z4,z5,z6])],[(0,[z0,z3,z4,z5,z1081,z6]),(0,[z0,z1,z4,z1082,z5,z6]),(0,[z0,z283,z243,z4,z5,z6]),(0,[z0,z1,z131,z4,z241,z6]),(0,[z0,z1083,z3,z4,z5,z6])],[(0,[z92,z0,z1,z3,z4,z396]),(0,[z0,z1,z62,z559,z4,z6]),(0,[z308,z1,z3,z4,z389,z5]),(0,[z0,z1,z1084,z4,z5,z6])]],
   [[(0,[z0,z1085,z1,z3,z4,z5]),(0,[z0,z1086,z3,z4,z5,z6]),(0,[z41,z205,z1,z3,z4,z6]),(0,[z0,z1,z3,z461,z4,z5]),(0,[z468,z1,z3,z4,z145,z6]),(0,[z0,z1,z1087,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1088])],[(0,[z0,z1,z3,z94,z5,z434]),(0,[z69,z92,z0,z3,z4,z5]),(0,[z482,z1,z3,z890,z5,z6]),(0,[z1089,z1,z3,z4,z5,z6]),(0,[z0,z27,z340,z4,z5,z134]),(0,[z68,z0,z1,z50,z4,z6])],[(0,[z0,z1,z1090,z4,z5,z6])],[(0,[z0,z1,z575,z74,z4,z5]),(0,[z0,z1,z1091,z4,z5,z6]),(0,[z68,z0,z89,z1,z51,z5]),(0,[z0,z1,z3,z74,z5,z748])],[(0,[z0,z1,z3,z4,z1092,z6]),(0,[z0,z1,z271,z786,z5,z6])],[(0,[z0,z1,z1093,z4,z5,z6]),(0,[z0,z1,z503,z4,z5,z73])],[(0,[z92,z0,z1,z4,z39,z5]),(0,[z0,z1,z3,z1094,z5,z6]),(0,[z0,z1,z3,z4,z217,z104])],[(0,[z1095,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z1096,z5,z6]),(0,[z43,z0,z1,z3,z374,z5])]],
   [[(0,[z69,z0,z4,z39,z5,z6]),(0,[z0,z1,z1097,z3,z4,z6]),(0,[z68,z0,z1,z51,z5,z6]),(0,[z0,z1,z3,z4,z145,z152])],[(0,[z0,z1,z1098,z4,z5,z6]),(0,[z0,z519,z3,z4,z5,z67])],[(1,[z1,z3,z4,z5,z977]),(0,[z43,z0,z1,z3,z5,z355]),(0,[z43,z40,z0,z1,z64,z3]),(0,[z40,z0,z1,z3,z17,z6]),(0,[z426,z0,z1,z3,z145,z5])],[(0,[z0,z1,z64,z3,z432,z136])],[(0,[z0,z23,z1,z4,z5,z445]),(0,[z0,z1,z3,z4,z5,z977]),(1,[z0,z725,z4,z5,z6]),(0,[z0,z1,z125,z4,z6,z245])],[(0,[z0,z1,z1099,z4,z5,z6]),(0,[z0,z288,z3,z4,z1028,z6]),(0,[z0,z3,z1100,z4,z5,z6]),(0,[z1101,z0,z1,z3,z4,z6]),(0,[z0,z223,z35,z3,z4,z5])],[(0,[z91,z483,z1,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1102]),(0,[z0,z1,z3,z5,z748,z44])],[(0,[z0,z1,z12,z153,z5,z6])]],
   [[(0,[z522,z1,z170,z4,z5,z6]),(0,[z0,z1,z1103,z4,z5,z6])],[(0,[z0,z1,z3,z4,z1104,z6]),(0,[z0,z1,z3,z4,z6,z1105]),(0,[z0,z1,z3,z1106,z5,z6]),(0,[z0,z1,z64,z3,z649,z4])],[(0,[z0,z1,z3,z4,z1107,z6]),(0,[z0,z654,z3,z4,z5,z134])],[(0,[z0,z1,z3,z4,z1108,z6]),(0,[z92,z0,z3,z4,z523,z5]),(0,[z0,z1,z3,z4,z5,z1109]),(0,[z0,z413,z3,z4,z169,z6])],[(0,[z0,z1,z243,z138,z4,z6]),(0,[z41,z1,z3,z4,z729,z6]),(0,[z1110,z1,z3,z4,z5,z6])],[(0,[z10,z88,z375,z4,z5,z6]),(0,[z0,z252,z1,z170,z4,z5]),(0,[z0,z1,z4,z5,z1111,z6]),(0,[z57,z444,z1,z3,z4,z6])],[(0,[z0,z1,z3,z4,z5,z1112]),(0,[z0,z1,z3,z4,z1113,z6])],[(0,[z0,z870,z3,z4,z5,z6]),(0,[z0,z3,z189,z481,z5,z6]),(0,[z0,z124,z3,z189,z5,z6]),(0,[z0,z1,z3,z4,z5,z1114]),(0,[z0,z1,z3,z4,z1115,z6])]],
   [[(0,[z0,z37,z243,z4,z5,z6]),(0,[z0,z27,z3,z4,z5,z134]),(0,[z436,z0,z1,z62,z4,z6]),(0,[z1116,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z1117,z6]),(0,[z31,z1,z3,z396,z13,z6]),(0,[z0,z1,z412,z4,z217,z6]),(0,[z0,z3,z189,z730,z5,z6]),(0,[z0,z66,z3,z539,z4,z5]),(0,[z0,z1,z1118,z3,z4,z6]),(0,[z43,z0,z1,z125,z3,z5])],[(0,[z10,z88,z3,z4,z5,z116]),(0,[z69,z0,z3,z281,z5,z6]),(0,[z225,z3,z4,z386,z169,z6]),(0,[z426,z0,z1,z3,z139,z6])],[(0,[z0,z1,z3,z4,z1119,z6]),(0,[z1,z3,z4,z5,z1120,z6])],[(1,[z1,z728,z4,z5,z6]),(0,[z0,z1,z4,z39,z5,z6]),(0,[z0,z1,z3,z5,z6,z1121]),(0,[z0,z450,z97,z4,z5,z6]),(0,[z40,z0,z1,z3,z368,z6])],[(0,[z0,z23,z1,z4,z5,z485]),(0,[z1122,z0,z1,z3,z5,z6]),(0,[z0,z27,z131,z4,z5,z134])],[(0,[z0,z1,z728,z4,z5,z6]),(0,[z0,z1,z1123,z4,z5,z6]),(0,[z308,z1,z3,z4,z5,z36]),(0,[z0,z3,z4,z5,z6,z778]),(0,[z0,z1,z3,z74,z330,z5])],[(0,[z0,z1,z1124,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z1125])]],
   [[(0,[z0,z1,z12,z4,z123,z6]),(0,[z0,z1,z3,z4,z1126,z5]),(0,[z0,z1,z3,z4,z1127,z6]),(0,[z40,z468,z1,z3,z4,z6])],[(0,[z0,z1,z3,z4,z5,z1128]),(0,[z0,z1,z3,z4,z5,z1129]),(0,[z10,z0,z252,z3,z4,z5]),(0,[z57,z1,z3,z381,z4,z6]),(0,[z0,z71,z97,z4,z5,z6])],[(0,[z1,z3,z728,z4,z5,z6]),(0,[z0,z23,z1,z138,z4,z6]),(0,[z308,z1,z575,z4,z5,z36]),(0,[z426,z0,z1,z64,z3,z6])],[(0,[z0,z1,z12,z4,z5,z434]),(0,[z0,z27,z3,z4,z5,z434]),(0,[z0,z1130,z1,z4,z5,z6]),(0,[z0,z1,z4,z1131,z5,z6]),(0,[z0,z1,z1132,z4,z5,z6])],[(0,[z0,z23,z223,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z1133])],[(0,[z0,z66,z3,z4,z5,z778]),(0,[z0,z1,z3,z4,z1134,z6]),(0,[z0,z1,z3,z4,z5,z1135])],[(0,[z0,z1,z1136,z4,z5,z6]),(0,[z0,z3,z1137,z4,z5,z6]),(0,[z0,z1,z1138,z4,z5,z6])],[(0,[z0,z1,z375,z4,z115,z6]),(0,[z0,z1,z3,z1139,z5,z6]),(0,[z0,z1,z24,z4,z5,z427]),(0,[z1140,z1,z3,z4,z5,z6]),(0,[z0,z1,z165,z786,z5,z6])]],
   [[(0,[z0,z1141,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z1142]),(0,[z1,z3,z4,z729,z5,z6]),(0,[z1143,z1,z3,z4,z5,z6]),(0,[z43,z0,z1,z3,z16,z44])],[(0,[z1144,z0,z1,z4,z5,z6]),(0,[z0,z498,z243,z4,z5,z6]),(0,[z0,z1,z3,z74,z5,z210])],[(0,[z0,z1,z1145,z4,z5,z6]),(0,[z0,z1,z1146,z4,z5,z6]),(0,[z0,z1,z3,z4,z1147,z6])],[(0,[z0,z288,z3,z4,z1076,z6]),(0,[z0,z1,z1148,z3,z4,z5])],[(0,[z0,z1,z3,z4,z115,z116]),(0,[z0,z1149,z1,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z1150]),(0,[z0,z694,z3,z4,z139,z6]),(0,[z0,z1,z62,z4,z433,z6])],[(0,[z0,z1,z1151,z4,z5,z6]),(0,[z0,z1,z64,z4,z258,z136])],[(0,[z0,z1,z3,z4,z5,z1152]),(0,[z0,z124,z3,z189,z5,z104])],[(0,[z308,z1,z3,z4,z5,z977]),(0,[z1153,z0,z1,z3,z5,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 544) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 544).take 546) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1090).take 15) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1105)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [544, 546, 15] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 132).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 132).take 124).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [132, 124] = true :=
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

end PEqualNP.Outside.L_meta_38253

theorem PEqualNP.Outside.L_meta_38253 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241864 * 2 ^ 32 + 3940597952) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241864 * 2 ^ 32 + 3940597952) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38253.solve