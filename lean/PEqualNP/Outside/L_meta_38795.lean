import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38795

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
  Nat.testBit (4276808426 * 2 ^ 32 + 4272605184) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x000004c2a80aae1d#64 ++ 0x20000098550155c3#64 ++ 0x8811cfc7e81ffe3f#64 ++ 0xd10239f8fd03ffc7#64 : BitVec 256),
   (0x08669259906662ee#64 ++ 0x410cd24b320ccc5d#64 ++ 0xf8eeb27990e667ff#64 ++ 0xbf1dd64f321cccff#64 : BitVec 256),
   (0x130b2c6e1b078747#64 ++ 0x8261658dc360f0e8#64 ++ 0xd70f3c7e1f0787c7#64 ++ 0x7ae1e78fc3e0f0f8#64 : BitVec 256),
   (0x25b03f800db805b0#64 ++ 0x04b607f001b700b6#64 ++ 0xbff03f801ff807fe#64 ++ 0xf7fe07f003ff00ff#64 : BitVec 256),
   (0x06dfc00016d55000#64 ++ 0x00dbf80002daaa00#64 ++ 0xffffc0001ffff805#64 ++ 0xfffff80003ffff00#64 : BitVec 256),
   (0x07fdfb3540000000#64 ++ 0x00ffbf66a8000000#64 ++ 0xe7ffffffe0000003#64 ++ 0xfcfffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [1, 2]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [9, 5]⟩, ⟨.and, [7, 10]⟩, ⟨.and, [8, 3]⟩, ⟨.or, [0, 12]⟩, ⟨.and, [13, 4]⟩, ⟨.or, [11, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x000004c2a80aae1d 0x20000098550155c3 0x8811cfc7e81ffe3f 0xd10239f8fd03ffc7

def z1 : W := mkw 0x06dfc00016d55000 0x00dbf80002daaa00 0xffffc0001ffff805 0xfffff80003ffff00

def z2 : W := mkw 0x07fdfb3540000000 0x00ffbf66a8000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z3 : W := mkw 0x08669259906662ee 0x410cd24b320ccc5d 0xf8eeb27990e667ff 0xbf1dd64f321cccff

def z4 : W := mkw 0x130b2c6e1b078747 0x8261658dc360f0e8 0xd71fffffff0787c7 0xfae3ffffffe0f0f8

def z5 : W := mkw 0x25b03f800db805b0 0x04b607f001b700b6 0xbff03f801ff807fe 0xf7fe07f003ff00ff

def z6 : W := mkw 0x0002000010040000 0x0000400002008000 0xd00e000010060005 0x3a01c0000200c000

def z7 : W := mkw 0x130b2c6e1b078747 0x8261658dc360f0e8 0xd70f3c7e1f0787c7 0x7ae1e78fc3e0f0f8

def z8 : W := mkw 0x0ffffb7dd06662ee 0x41ffff6fba0ccc5d 0xfffffffff0e667ff 0xfffffffffe1cccff

def z9 : W := mkw 0x00649211002000a0 0x000c924220040014 0xf8eeb27990e007ff 0xbf1dd64f321c00ff

def z10 : W := mkw 0x08669219106440e2 0x410cd243220c881c 0xf8ee323810e007fe 0xbf1dc647021c00ff

def z11 : W := mkw 0x124fc06e1247d247 0x8249f80dc248fa48 0x400fc07e0007f801 0x0801f80fc000ff00

def z12 : W := mkw 0x04d4c00004d05000 0x009a9800009a0a00 0x28f0c00000f87800 0x851e1800001f0f00

def z13 : W := mkw 0x08649211806060a8 0x410c9242300c0c15 0x28e0820180e06038 0x851c1040301c0c07

def z14 : W := mkw 0x0000048008080410 0x0000009001010082 0x8811cfc7e818063f 0xd10239f8fd0300c7

def z15 : W := mkw 0x130b282c13050142 0x826165058260a028 0xd70f3c7e170001c3 0x7ae1e78fc2e00038

def z16 : W := mkw 0x130b2ceebb0faf5f 0xa261659dd761f5eb 0xdf1fffffff1fffff 0xfbe3ffffffe3ffff

def z17 : W := mkw 0x24b0138004b800b0 0x0496027000970016 0x28f0038000f80038 0x851e0070001f0007

def z18 : W := mkw 0x00201200002000a0 0x0004024000040014 0xb8e0320010e007fe 0xb71c0640021c00ff

def z19 : W := mkw 0x0064921100000000 0x000c924220000000 0xe0eeb27980000003 0xbc1dd64f30000000

def z20 : W := mkw 0x0edfc05996d7724e 0x41dbf80b32daee49 0xffffc0799ffff805 0xfffff80f33ffff00

def z21 : W := mkw 0x0699400006911000 0x00d3280000d22200 0x071140000f199800 0x40e2280001e33300

def z22 : W := mkw 0x08201259802222ee 0x4104024b3004445d 0x00003279800007fa 0x0000064f300000ff

def z23 : W := mkw 0x03092ce6a80aae1d 0x2061259cd50155c3 0xcf1fffffe81ffe3f 0xf9e3fffffd03ffc7

def z24 : W := mkw 0x24f4d39144b800b0 0x049e9a7228970016 0x28f0c381e0f80038 0x851e18703c1f0007

def z25 : W := mkw 0x00000482a808ac19 0x2000009055011583 0x0811cf87e819f838 0xc10239f0fd033f07

def z26 : W := mkw 0x002016c2a82aaebd 0x200402d8550555d7 0xb8f1ffc7f8ffffff 0xf71e3ff8ff1fffff

def z27 : W := mkw 0x37bb3fee1fbf87f7 0x86f767fdc3f7f0fe 0xffff3ffe1fff87ff 0xffffe7ffc3fff0ff

def z28 : W := mkw 0x03092c6608028605 0x0061258cc10050c0 0xc70f3c7e08078607 0x78e1e78fc100f0c0

def z29 : W := mkw 0x000000408002220c 0x0000000810004441 0x880082418006663f 0x910010483000ccc7

def z30 : W := mkw 0x130b2c2e1b058543 0x82616585c360b0a8 0x570f3c3e1f0181c0 0x6ae1e787c3e03038

def z31 : W := mkw 0x0309282400000000 0x0061250480000000 0xc70f3c7e00000003 0x78e1e78fc0000000

def z32 : W := mkw 0x0799692446911000 0x00f32d2488d22200 0x07114d866f199800 0x40e229b0cde33300

def z33 : W := mkw 0x20201380002800b0 0x0404027000050016 0x0000038000000038 0x0000007000000007

def z34 : W := mkw 0x0cf6d25994f672ee 0x419eda4b329ece5d 0xf8fef27990fe7fff 0xbf1fde4f321fcfff

def z35 : W := mkw 0x0490000004900000 0x0092000000920000 0xbff000001ff80004 0xf7fe000003ff0000

def z36 : W := mkw 0x07fdfb3544900000 0x00ffbf66a8920000 0xfffffffffff80007 0xffffffffffff0000

def z37 : W := mkw 0x1002044a1b078747 0x820040894360f0e8 0x100000001f0787c4 0x0200000003e0f0f8

def z38 : W := mkw 0x0000000000000000 0x0000000000000000 0x8011cfc7e0000003 0xd00239f8fc000000

def z39 : W := mkw 0x07fdfff7e80aae1d 0x20ffbffefd0155c3 0xefffffffe81ffe3f 0xfdfffffffd03ffc7

def z40 : W := mkw 0x0064921100000000 0x000c924220000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z41 : W := mkw 0x086696dbb86eeeff 0x610cd2db770ddddf 0xf8fffffff8ffffff 0xff1fffffff1fffff

def z42 : W := mkw 0x0000044208028605 0x00000088410050c0 0x80010c4608078607 0x50002188c100f0c0

def z43 : W := mkw 0x179b2c6e1f978747 0x82f3658dc3f2f0e8 0xffff3c7e1fff87c7 0xffffe78fc3fff0f8

def z44 : W := mkw 0x024dc03540000000 0x0049b806a8000000 0x400fc07fe0000001 0x0801f80ffc000000

def z45 : W := mkw 0x27fdffb54db805b0 0x04ffbff6a9b700b6 0xfffffffffff807ff 0xffffffffffff00ff

def z46 : W := mkw 0x37992da60f998511 0x86f325b4c1f330a2 0x07110d860f198000 0x40e221b0c1e33000

def z47 : W := mkw 0x25b03f80adb82db8 0x24b607f015b705b7 0xbff0ff81fff87ffe 0xf7fe1ff03fff0fff

def z48 : W := mkw 0x0046800010444000 0x0008d00002088800 0xf8ee800010e66005 0xbf1dd000021ccc00

def z49 : W := mkw 0x0effd25996f772ee 0x41dffa4b32deee5d 0xfffff2799fffffff 0xfffffe4f33ffffff

def z50 : W := mkw 0x020b000012050000 0x004160000240a000 0xd70f00001f078005 0x7ae1e00003e0f000

def z51 : W := mkw 0x11002c6e09028747 0x8220058dc12050e8 0x00003c7e000007c2 0x0000078fc00000f8

def z52 : W := mkw 0x07dde82400000000 0x00fbbd0480000000 0xe7fffc7e00000003 0xfcffff8fc0000000

def z53 : W := mkw 0x07fdfb35402000a0 0x00ffbf66a8040014 0xfffffffff0e007ff 0xfffffffffe1c00ff

def z54 : W := mkw 0x024fc00012455000 0x0049f8000248aa00 0x400e000000000000 0x0801c00000000000

def z55 : W := mkw 0x17ffff7f5b078747 0x82ffffefeb60f0e8 0xf7ef3c7e1f0787c7 0x7efde78fc3e0f0f8

def z56 : W := mkw 0x0100280001000100 0x0020050000200020 0x17003000170001c0 0x22e0060002e00038

def z57 : W := mkw 0x08669219906460ea 0x410cd243320c8c1d 0x78eeb23990e061f8 0xaf1dd647321c0c3f

def z58 : W := mkw 0x130b282c13050142 0x826165058260a028 0x570e3038170001c0 0x2ae1c60702e00038

def z59 : W := mkw 0x24b017800cb804b0 0x049602f001970096 0xa8f00f8008f8063e 0xd51e01f0011f00c7

def z60 : W := mkw 0x0000000006911000 0x0000000000d22200 0x000000000f199800 0x0000000001e33300

def z61 : W := mkw 0x0209000002010000 0x0041200000402000 0x070100000f018000 0x40e0200001e03000

def z62 : W := mkw 0x0ffdfb7dc02222ee 0x41ffbf6fb804445d 0xe7ffffffe00007fb 0xfcfffffffc0000ff

def z63 : W := mkw 0x084680599046624e 0x4108d00b3208cc49 0x400e807980066001 0x0801d00f3000cc00

def z64 : W := mkw 0x25902d800d980510 0x04b205b001b300a2 0x07100d800f180000 0x40e201b001e30000

def z65 : W := mkw 0x020b004812070246 0x004160090240e048 0xd70f30781f0787c7 0x7ae1e60f03e0f0f8

def z66 : W := mkw 0x25902dc2ad9aaf1d 0x24b205b855b355e3 0x8f11cfc7ef1ffe3f 0xd1e239f8fde3ffc7

def z67 : W := mkw 0x0490000004900000 0x0092000000920000 0x37e0000017e00000 0x26fc000002fc0000

def z68 : W := mkw 0x08020008106440e2 0x41004001020c881c 0x1000000010e001c0 0x02000000021c0038

def z69 : W := mkw 0x200004800db805b0 0x0400009001b700b6 0x98100f801ff807fe 0xd30201f003ff00ff

def z70 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z71 : W := mkw 0x03293b3540000000 0x00652766a8000000 0xc70f3fffe0000003 0x78e1e7fffc000000

def z72 : W := mkw 0x35b03fee0dba87f7 0x86b607fdc1b750fe 0xbff03ffe1ff807fe 0xf7fe07ffc3ff00ff

def z73 : W := mkw 0x0844801180406008 0x4108900230080c01 0x0000800180006000 0x0000100030000c00

def z74 : W := mkw 0x000004c2a80aae1d 0x20000098550155c3 0x00000fc7e000063a 0x000001f8fc0000c7

def z75 : W := mkw 0x06dfc4c2bedffe1d 0x20dbf89857dbffc3 0xffffcfc7fffffe3f 0xfffff9f8ffffffc7

def z76 : W := mkw 0x130b2c6e9b07a74f 0x8261658dd360f4e9 0xdf0fbe7f9f07e7ff 0xfbe1f7cff3e0fcff

def z77 : W := mkw 0x0000048228088c11 0x2000009045011182 0x00114d8668199800 0x400229b0cd033300

def z78 : W := mkw 0x08669219106440e2 0x410cd243220c881c 0x70ee303810e001c0 0x2e1dc607021c0038

def z79 : W := mkw 0x1b6fbe7f1b67c7e7 0xc36df7cfe36cf8fc 0xf7ef3c7e1fe787c7 0x7efde78fc3fcf0f8

def z80 : W := mkw 0x06ddc00000000000 0x00dbb80000000000 0xe7ffc00000000001 0xfcfff80000000000

def z81 : W := mkw 0x07fffb3556d55000 0x00ffff66aadaaa00 0xfffffffffffff807 0xffffffffffffff00

def z82 : W := mkw 0x000004c2a80aae1d 0x20000098550155c3 0x8011cfc7e000063b 0xd00239f8fc0000c7

def z83 : W := mkw 0x000004c2a80aae1d 0x20000098550155c3 0x88100fc7e818063e 0xd10201f8fd0300c7

def z84 : W := mkw 0x07fdfb3540000000 0x00ffbf66a8000000 0x67eff07fe0000001 0x2cfdfe0ffc000000

def z85 : W := mkw 0x0799692440000000 0x00f32d2488000000 0xc71f7dfe60000003 0x78e3efbfcc000000

def z86 : W := mkw 0x2000000005b001a0 0x0400000000b60034 0x1000000017e001c0 0x0200000002fc0038

def z87 : W := mkw 0x0002004810060246 0x000040090200c048 0xd00e3078100607c7 0x3a01c60f0200c0f8

def z88 : W := mkw 0x17dfec6e1fd7d747 0x82fbfd8dc3fafae8 0xfffffc7e1fffffc7 0xffffff8fc3fffff8

def z89 : W := mkw 0x1309282403010100 0x8261250480602020 0x0700000007000000 0x00e0000000e00000

def z90 : W := mkw 0x06dfc04816d75246 0x00dbf80902daea48 0xfffff0781fffffc7 0xfffffe0f03fffff8

def z91 : W := mkw 0x1b6fbe7f9b67e7ef 0xc36df7cff36cfcfd 0xffefbe7f9fe7e7ff 0xfffdf7cff3fcfcff

def z92 : W := mkw 0x01203b3540000000 0x00240766a8000000 0x0000303800000000 0x0000060700000000

def z93 : W := mkw 0x25b03b0005b001a0 0x04b6076000b60034 0xbfe0320017e007fe 0xb7fc064002fc00ff

def z94 : W := mkw 0x25b03fb54db805b0 0x04b607f6a9b700b6 0xbff03ffffff807fe 0xf7fe07ffffff00ff

def z95 : W := mkw 0x0002004810060246 0x000040090200c048 0x400e007800060001 0x0801c00f0000c000

def z96 : W := mkw 0x17ffff7f5fd7d747 0x82ffffefebfafae8 0xffffffffffffffc7 0xfffffffffffffff8

def z97 : W := mkw 0x27996d800f991510 0x04f32db001f322a2 0x07114d800f199800 0x40e229b001e33300

def z98 : W := mkw 0x0000000000000000 0x0000000000000000 0x8811c000081ff805 0xd10238000103ff00

def z99 : W := mkw 0x08669259906662ee 0x410cd24b320ccc5d 0xf8fff27998ffffff 0xff1ffe4f331fffff

def z100 : W := mkw 0x0ffffffff86eeeff 0x61ffffffff0ddddf 0xfffffffff8ffffff 0xffffffffff1fffff

def z101 : W := mkw 0x086696d9986e66fe 0x410cd2db330dccdf 0xf8febff998fe67ff 0xff1fd7ff331fccff

def z102 : W := mkw 0x120b006e12078247 0x8241600dc240f048 0xd70f007e1f078005 0x7ae1e00fc3e0f000

def z103 : W := mkw 0x04f4d31140000000 0x009e9a6228000000 0x20f0c381e0000000 0x841e18703c000000

def z104 : W := mkw 0x17ffff7f5b078747 0x82ffffefeb60f0e8 0xf7ffffffff0787c7 0xfeffffffffe0f0f8

def z105 : W := mkw 0x16dfc44a1fd7d747 0x82dbf88943fafae8 0xffffc0001fffffc5 0xfffff80003fffff8

def z106 : W := mkw 0x084684dbb84eee5f 0x6108d09b7709ddcb 0xc81fcfffe81ffe3f 0xd903f9fffd03ffc7

def z107 : W := mkw 0x07fdfb3540000000 0x00ffbf66a8000000 0xefffffffe81ff807 0xfdfffffffd03ff00

def z108 : W := mkw 0x08020048906662ee 0x41004009120ccc5d 0x1800000010e667fc 0x03000000021cccff

def z109 : W := mkw 0x130b2cee3b0f8f57 0xa261659dc761f1ea 0xd71f7dfe7f1f9fc7 0x7ae3efbfcfe3f3f8

def z110 : W := mkw 0x0000048008080410 0x0000009001010082 0x8811cf80081ffe3f 0xd10239f00103ffc7

def z111 : W := mkw 0x13092c260b018501 0x82612584c16030a0 0x07010c060f018000 0x40e02180c1e03000

def z112 : W := mkw 0x0799692440000000 0x00f32d2488000000 0x07114d8660000000 0x40e229b0cc000000

def z113 : W := mkw 0x24b0130004b000a0 0x0496026000960014 0x20e0000000e00000 0x041c0000001c0000

def z114 : W := mkw 0x01203b3540000000 0x00240766a8000000 0x00003fffe0000002 0x000007fffc000000

def z115 : W := mkw 0x249004800db805b0 0x0492009001b700b6 0xbff000001ff807fc 0xf7fe000003ff00ff

def z116 : W := mkw 0x37ffffff5fbf87f7 0x86ffffffebf7f0fe 0xffffffffffff87ff 0xfffffffffffff0ff

def z117 : W := mkw 0x09203b7dc02222ee 0x4124076fb804445d 0x00003fffe00007fa 0x000007fffc0000ff

def z118 : W := mkw 0x17fffffffb0faf5f 0xa2ffffffff61f5eb 0xffffffffff1fffff 0xffffffffffe3ffff

def z119 : W := mkw 0x05b03b0000000000 0x00b6076000000000 0xa7f03f8000000002 0xf4fe07f000000000

def z120 : W := mkw 0x00000042a002aa0d 0x2000000854005541 0x0001c047e007f801 0x00003808fc00ff00

def z121 : W := mkw 0x130b2c6ebb07af4f 0xa261658dd760f5e9 0xd70ffc7fff07ffc7 0x7ae1ff8fffe0fff8

def z122 : W := mkw 0x0002000010444000 0x0000400002088800 0x1800000010e66004 0x03000000021ccc00

def z123 : W := mkw 0x0000000000000000 0x0000000000000000 0x0001c0000007f801 0x000038000000ff00

def z124 : W := mkw 0x0000000000000000 0x0000000000000000 0x880002000000063e 0x91000040000000c7

def z125 : W := mkw 0x0000040208008401 0x0000008041001080 0x00010c0608018000 0x40002180c1003000

def z126 : W := mkw 0x0a4fc0599247724e 0x4149f80b3248ee49 0x400fc0798007f801 0x0801f80f3000ff00

def z127 : W := mkw 0x000000408002220c 0x0000000810004441 0x8811cfc7e006663f 0xd10239f8fc00ccc7

def z128 : W := mkw 0x0309282400000000 0x0061250480000000 0x07010c0600000000 0x40e02180c0000000

def z129 : W := mkw 0x07dfe82416d55000 0x00fbfd0482daaa00 0xfffffc7e1ffff807 0xffffff8fc3ffff00

def z130 : W := mkw 0x19203e7f8922a7ef 0xc32407cff12454fd 0x00003e7f800007fa 0x000007cff00000ff

def z131 : W := mkw 0x2df6bfd99dfe67fe 0x45bed7fb33bfccff 0xfffebff99ffe67ff 0xffffd7ff33ffccff

def z132 : W := mkw 0x080204cab86eeeff 0x61004099570ddddf 0x1800000018fffffc 0x03000000031fffff

def z133 : W := mkw 0x01002c0009000500 0x00200580012000a0 0x97003c001f0007c6 0x72e0078003e000f8

def z134 : W := mkw 0x130b2c6e1b078747 0x8261658dc360f0e8 0x570e3c7e170007c2 0x2ae1c78fc2e000f8

def z135 : W := mkw 0x1b6fbeffbb6fefff 0xe36df7dff76dfdff 0xffffffffffffffff 0xffffffffffffffff

def z136 : W := mkw 0x37bb3f6e1fb787e7 0x86f767edc3f6f0fc 0xf7ef3c7e1fe787c7 0x7efde78fc3fcf0f8

def z137 : W := mkw 0x120b04eeba0fae5f 0xa241609dd741f5cb 0xc81fcfffe81ffe3f 0xd903f9fffd03ffc7

def z138 : W := mkw 0x27ffff801ffd55b0 0x04fffff003ffaab6 0xffffff801fffffff 0xfffffff003ffffff

def z139 : W := mkw 0x086692d9b06e6afe 0x610cd25b360dcd5f 0xf8fef3f9f0fe7fff 0xbf1fde7f3e1fcfff

def z140 : W := mkw 0x1a4f807f9247e24f 0xc349f00ff248fc49 0x400f807f8007e001 0x0801f00ff000fc00

def z141 : W := mkw 0x24b0138004b800b0 0x0496027000970016 0xb8f0338010f807fe 0xb71e0670021f00ff

def z142 : W := mkw 0x06dfc00016d55000 0x00dbf80002daaa00 0xffffcfc7fffff807 0xfffff9f8ffffff00

def z143 : W := mkw 0x25b03b0005b001a0 0x04b6076000b60034 0x37e0300017e001c0 0x26fc060002fc0038

def z144 : W := mkw 0x27fdff800db805b0 0x04ffbff001b700b6 0xffffff801ff807ff 0xfffffff003ff00ff

def z145 : W := mkw 0x024dc077e002aa0d 0x2049b80efc005541 0x400fc07fe007f801 0x0801f80ffc00ff00

def z146 : W := mkw 0x00000080a0082818 0x2000001014010503 0x0810c381e0187838 0x810218703c030f07

def z147 : W := mkw 0x000004c2a80aae1d 0x20000098550155c3 0x88100f80081ffe3e 0xd10201f00103ffc7

def z148 : W := mkw 0x07fffb7d50060246 0x00ffff6faa00c048 0xf7fffffff00607c7 0xfefffffffe00c0f8

def z149 : W := mkw 0x08669259906662ee 0x410cd24b320ccc5d 0x78ee303810e667fc 0x2f1dc607021cccff

def z150 : W := mkw 0x27fdfff7edbaafbd 0x24ffbffefdb755f7 0xffffffffffffffff 0xffffffffffffffff

def z151 : W := mkw 0x130b2ceebb0faf5f 0xa261659dd761f5eb 0xdf0f3c7e1f1fffff 0x7be1e78fc3e3ffff

def z152 : W := mkw 0x04b0120004b000a0 0x0096024000960014 0xbff032001ff807fe 0xf7fe064003ff00ff

def z153 : W := mkw 0x07fdfb3540000000 0x00ffbf66a8000000 0x27f1cf87e0000000 0xc4fe39f0fc000000

def z154 : W := mkw 0x00201200002000a0 0x0004024000040014 0x28e0020000e00038 0x851c0040001c0007

def z155 : W := mkw 0x084680599046624e 0x4108d00b3208cc49 0xf8ee807990e66005 0xbf1dd00f321ccc00

def z156 : W := mkw 0x07dde93540000000 0x00fbbd26a8000000 0x471fcdffe0000001 0x48e3f9bffc000000

def z157 : W := mkw 0x1b4fac7f9b47e74f 0xc369f58ff368fce9 0xd70fbc7f9f07e7c7 0x7ae1f78ff3e0fcf8

def z158 : W := mkw 0x00000042a002aa0d 0x2000000854005541 0x000000000007f800 0x000000000000ff00

def z159 : W := mkw 0x05b03b0000000000 0x00b6076000000000 0x27e0300000000000 0x24fc060000000000

def z160 : W := mkw 0x08649211006040a0 0x410c9242200c0814 0x20e0000000e00000 0x041c0000001c0000

def z161 : W := mkw 0x134fac6e1b47c747 0x8269f58dc368f8e8 0xffefbc7e1fe7e7c7 0xfffdf78fc3fcfcf8

def z162 : W := mkw 0x0002004810060246 0x000040090200c048 0x10000000100607c4 0x020000000200c0f8

def z163 : W := mkw 0x06dfc080b6dd7818 0x20dbf81016dbaf03 0xffffc381fffff83d 0xfffff8703fffff07

def z164 : W := mkw 0x25b03fc2adbaafbd 0x24b607f855b755f7 0xbff1ffc7ffffffff 0xf7fe3ff8ffffffff

def z165 : W := mkw 0x06ddc00004900000 0x00dbb80000920000 0xffffc0001ff80005 0xfffff80003ff0000

def z166 : W := mkw 0x000004c2a80aae1d 0x20000098550155c3 0x08000000081ffe3c 0x010000000103ffc7

def z167 : W := mkw 0x17bb3f6e1b078747 0x82f767edc360f0e8 0xf7ff3ffe1f0787c7 0xfeffe7ffc3e0f0f8

def z168 : W := mkw 0x25b03f800db805b0 0x04b607f001b700b6 0xbff1ff801fffffff 0xf7fe3ff003ffffff

def z169 : W := mkw 0x06dfc00016d55000 0x00dbf80002daaa00 0x7fee00001ffff804 0x2ffdc00003ffff00

def z170 : W := mkw 0x06ddc4c2a80aae1d 0x20dbb898550155c3 0xefffcfc7e81ffe3f 0xfdfff9f8fd03ffc7

def z171 : W := mkw 0x08669211906460a8 0x410cd242320c8c15 0xf8ee820190e6603d 0xbf1dd040321ccc07

def z172 : W := mkw 0x25b03b8004b800b0 0x04b6077000970016 0xaff03f8000f8003a 0xf5fe07f0001f0007

def z173 : W := mkw 0x030b286c10060246 0x0061650d8200c048 0xd70f3c7e100607c7 0x7ae1e78fc200c0f8

def z174 : W := mkw 0x04d4c00004d05000 0x009a9800009a0a00 0xa8f1c00008fff805 0xd51e3800011fff00

def z175 : W := mkw 0x0000044208028605 0x00000088410050c0 0x8811cc46081ffe07 0xd1023988c103ffc0

def z176 : W := mkw 0x17fffb3d53050142 0x82ffff67aa60a028 0x77ee3038170001c0 0x2efdc60702e00038

def z177 : W := mkw 0x120b006e12078247 0x8241600dc240f048 0x400f007e00078001 0x0801e00fc000f000

def z178 : W := mkw 0x21203fc2a92aafbd 0x242407f8552555f7 0x00003fc7e00007fa 0x000007f8fc0000ff

def z179 : W := mkw 0x25b03fc20dba87b5 0x04b607f841b750f6 0xbff13fc61fff87ff 0xf7fe27f8c3fff0ff

def z180 : W := mkw 0x07fdfb3546911000 0x00ffbf66a8d22200 0xe7ffffffef199803 0xfcfffffffde33300

def z181 : W := mkw 0x200004800db805b0 0x0400009001b700b6 0x180000001ff807fc 0x0300000003ff00ff

def z182 : W := mkw 0x0000008020080810 0x2000001004010102 0x0010418060181800 0x000208300c030300

def z183 : W := mkw 0x004684c2b84eee1d 0x2008d0985709ddc3 0xf8ffcfc7f8fffe3f 0xff1ff9f8ff1fffc7

def z184 : W := mkw 0x37ffffee1fffd7f7 0x86fffffdc3fffafe 0xfffffffe1fffffff 0xffffffffc3ffffff

def z185 : W := mkw 0x0044801100000000 0x0008900220000000 0x400e807980000001 0x0801d00f30000000

def z186 : W := mkw 0x000004c2a80aae1d 0x20000098550155c3 0x88010c46081ffe3f 0x51002188c103ffc7

def z187 : W := mkw 0x21203f80092805b0 0x042407f0012500b6 0x00003f80000007fa 0x000007f0000000ff

def z188 : W := mkw 0x21203f80092805b0 0x042407f0012500b6 0xb8e03f8010e007fe 0xb71c07f0021c00ff

def z189 : W := mkw 0x27fffb0017f551a0 0x04ffff6002feaa34 0x77ee300017e001c0 0x2efdc60002fc0038

def z190 : W := mkw 0x08020048906662ee 0x41004009120ccc5d 0xd80e307810e667ff 0x3b01c60f021cccff

def z191 : W := mkw 0x0df6bb59906662ee 0x41bed76b320ccc5d 0xfffebff990e667ff 0xffffd7ff321cccff

def z192 : W := mkw 0x1b6fba3d136541e2 0xc36df747a26ca83c 0x77ee303817e001c0 0x2efdc60702fc0038

def z193 : W := mkw 0x100204cabb0faf5f 0xa20040995761f5eb 0x180000001f1ffffc 0x0300000003e3ffff

def z194 : W := mkw 0x120b044a1b078747 0x824160894360f0e8 0xd70f00001f0787c5 0x7ae1e00003e0f0f8

def z195 : W := mkw 0x00221248102602e6 0x000442490204c05c 0xf8ee327810e607ff 0xbf1dc64f021cc0ff

def z196 : W := mkw 0x200204801ffd55b0 0x0400409003ffaab6 0x180000001ffffffc 0x0300000003ffffff

def z197 : W := mkw 0x27996da44d980510 0x04f32db489b300a2 0x07114d866f180000 0x40e229b0cde30000

def z198 : W := mkw 0x024fc00012455000 0x0049f8000248aa00 0xf8efc00010e7f805 0xbf1df800021cff00

def z199 : W := mkw 0x01002cc2a90aaf1d 0x20200598552155e3 0x9f11ffc7ff1fffff 0xf3e23ff8ffe3ffff

def z200 : W := mkw 0x0309282400000000 0x0061250480000000 0xc71fffffe0000003 0xf8e3fffffc000000

def z201 : W := mkw 0x01002c4209028705 0x00200588412050e0 0x97013c461f0787c7 0x72e02788c3e0f0f8

def z202 : W := mkw 0x06ddc00004d05000 0x00dbb800009a0a00 0xefffc00000f87801 0xfdfff800001f0f00

def z203 : W := mkw 0x130b2c6e1b078747 0x8261658dc360f0e8 0xdf1ffc7e1f1fffc7 0xfbe3ff8fc3e3fff8

def z204 : W := mkw 0x0799692440000000 0x00f32d2488000000 0x8711cfc7e0000003 0xd0e239f8fc000000

def z205 : W := mkw 0x27ffffb55ffd55b0 0x04fffff6abffaab6 0xffffffffffffffff 0xffffffffffffffff

def z206 : W := mkw 0x024fc00012455000 0x0049f8000248aa00 0x400fc0000007f801 0x0801f8000000ff00

def z207 : W := mkw 0x0ffffb3d506440e2 0x41ffff67aa0c881c 0x77ee303810e001c0 0x2efdc607021c0038

def z208 : W := mkw 0x25b03f800db805b0 0x04b607f001b700b6 0x3fe030001ff807fc 0x27fc060003ff00ff

def z209 : W := mkw 0x04f4d391e0082818 0x209e9a723c010503 0x28f0c381e0187838 0x851e18703c030f07

def z210 : W := mkw 0x120b006eb207aa4f 0xa241600dd640f549 0x400fc07fe007f801 0x0801f80ffc00ff00

def z211 : W := mkw 0x21203f800db805b0 0x042407f001b700b6 0x18003f801ff807fe 0x030007f003ff00ff

def z212 : W := mkw 0x0000000000000000 0x0000000000000000 0x8811cfc7e81ff807 0xd10239f8fd03ff00

def z213 : W := mkw 0x049004c2ac9aae1d 0x20920098559355c3 0xbff1cfc7fffffe3f 0xf7fe39f8ffffffc7

def z214 : W := mkw 0x27ffff801ffd55b0 0x04fffff003ffaab6 0xfffe3f801ff807fe 0xffffc7f003ff00ff

def z215 : W := mkw 0x04f4d31140000000 0x009e9a6228000000 0x20e0000000000000 0x041c000000000000

def z216 : W := mkw 0x01002c8009080510 0x00200590012100a2 0x9f103f801f1807fe 0xf3e207f003e300ff

def z217 : W := mkw 0x0ffffb7dd6f772ee 0x41ffff6fbadeee5d 0xffffffffffffffff 0xffffffffffffffff

def z218 : W := mkw 0x06dfc03556d55000 0x00dbf806aadaaa00 0xffffc07ffffff805 0xfffff80fffffff00

def z219 : W := mkw 0x379b2dee1f9f8757 0x86f365bdc3f3f0ea 0xd71f3dfe1f1f87c7 0x7ae3e7bfc3e3f0f8

def z220 : W := mkw 0x0effd25996f772ee 0x41dffa4b32deee5d 0xffeeb27997e667ff 0xbffdd64f32fcccff

def z221 : W := mkw 0x0002000016d55000 0x0000400002daaa00 0x180000001ffff804 0x0300000003ffff00

def z222 : W := mkw 0x06dfc00016d55000 0x00dbf80002daaa00 0x77ee000017e00000 0x2efdc00002fc0000

def z223 : W := mkw 0x01203ff7e80aae1d 0x202407fefd0155c3 0x8811ffffe81ffe3f 0xd1023ffffd03ffc7

def z224 : W := mkw 0x11022c6e19068747 0x8220458dc320d0e8 0xd00e3c7e100607c7 0x3a01c78fc200c0f8

def z225 : W := mkw 0x1966be7f9966e7ef 0xc32cd7cff32cdcfd 0xf8eebe7f90e667ff 0xbf1dd7cff21cccff

def z226 : W := mkw 0x06ddc00006911000 0x00dbb80000d22200 0xe7ffc0000f199801 0xfcfff80001e33300

def z227 : W := mkw 0x1000044a09028747 0x82000089412050e8 0x00000000000007c0 0x00000000000000f8

def z228 : W := mkw 0x0799692440000000 0x00f32d2488000000 0x0700000000000000 0x00e0000000000000

def z229 : W := mkw 0x120b002c12050042 0x824160058240a008 0x400e003800000000 0x0801c00700000000

def z230 : W := mkw 0x0866925bb066eaef 0x610cd24b760cdd5d 0xf8eff27ff0e7ffff 0xbf1dfe4ffe1cffff

def z231 : W := mkw 0x21203fc2a92aafbd 0x242407f8552555f7 0x8811ffc7e81fffff 0xd1023ff8fd03ffff

def z232 : W := mkw 0x27fdffb54d980510 0x04ffbff6a9b300a2 0xe7ffffffef180003 0xfcfffffffde30000

def z233 : W := mkw 0x06ddc00000000000 0x00dbb80000000000 0xefffc000081ff805 0xfdfff8000103ff00

def z234 : W := mkw 0x08201259802222ee 0x4104024b3004445d 0x8800b279800667ff 0x9100164f3000ccff

def z235 : W := mkw 0x000004c2a80aae1d 0x20000098550155c3 0x0001cfc7e007fe3b 0x000039f8fc00ffc7

def z236 : W := mkw 0x37b93fa60fb985b1 0x86f727f4c1f730b6 0xbff13f861ff987fe 0xf7fe27f0c3ff30ff

def z237 : W := mkw 0x130b2ceebb0faf5f 0xa261659dd761f5eb 0xd70f3fffff0787ff 0x7ae1e7ffffe0f0ff

def z238 : W := mkw 0x07fdfb3540000000 0x00ffbf66a8000000 0x67ee303800000000 0x2cfdc60700000000

def z239 : W := mkw 0x00000042a002aa0d 0x2000000854005541 0x8011cfc7e007f803 0xd00239f8fc00ff00

def z240 : W := mkw 0x100004020b018501 0x82000080416030a0 0x000000000f018000 0x0000000001e03000

def z241 : W := mkw 0x0b6fba7d906662ee 0x416df74fb20ccc5d 0xffefbe7f90e667ff 0xfffdf7cff21cccff

def z242 : W := mkw 0x030b2c001b050500 0x006165800360a0a0 0xd70f3c001f0787c7 0x7ae1e78003e0f0f8

def z243 : W := mkw 0x080200489046624e 0x410040091208cc49 0x0000000000066000 0x000000000000cc00

def z244 : W := mkw 0x0046800010444000 0x0008d00002088800 0xf8ffc00018fff805 0xff1ff800031fff00

def z245 : W := mkw 0x130b286c13070346 0x8261650d8260e068 0xd70e3078170607c7 0x3ae1c60f02e0c0f8

def z246 : W := mkw 0x25902d822d988d11 0x24b205b045b311a2 0x07114d866f199800 0x40e229b0cde33300

def z247 : W := mkw 0x024dc03540000000 0x0049b806a8000000 0xc01fcfffe0000003 0xd803f9fffc000000

def z248 : W := mkw 0x0492000016d55000 0x0092400002daaa00 0xbff000001ffff804 0xf7fe000003ffff00

def z249 : W := mkw 0x0ffdfb35c06060a8 0x41ffbf66b80c0c15 0xefffffffe0e0603b 0xfdfffffffc1c0c07

def z250 : W := mkw 0x0000000220008801 0x2000000044001100 0x0001400660019800 0x00002800cc003300

def z251 : W := mkw 0x024fc03552455000 0x0049f806aa48aa00 0x400fc07fe007f801 0x0801f80ffc00ff00

def z252 : W := mkw 0x07fffb3550444000 0x00ffff66aa088800 0xfffffffff0e66007 0xfffffffffe1ccc00

def z253 : W := mkw 0x08649259806262ee 0x410c924b300c4c5d 0x28e0b27980e067fa 0x851c164f301c0cff

def z254 : W := mkw 0x202016800db805b0 0x040402d001b700b6 0xb8e032001ff807fe 0xb71c064003ff00ff

def z255 : W := mkw 0x1866965b9b67e7ef 0xc30cd2cb736cfcfd 0xf8eeb2799fe7e7ff 0xbf1dd64f33fcfcff

def z256 : W := mkw 0x05f4bb1100000000 0x00be976220000000 0xe7febff980000003 0xfcffd7ff30000000

def z257 : W := mkw 0x37bb3feebfbfafff 0xa6f767fdd7f7f5ff 0xffffffffffffffff 0xffffffffffffffff

def z258 : W := mkw 0x17fffb3d53050142 0x82ffff67aa60a028 0xf7fffffff70001c3 0xfefffffffee00038

def z259 : W := mkw 0x06dfc00016d55000 0x00dbf80002daaa00 0xfffe00001ff80004 0xffffc00003ff0000

def z260 : W := mkw 0x179b6d6e5b078747 0x82f36dadcb60f0e8 0xd71f7dfe7f0787c7 0x7ae3efbfcfe0f0f8

def z261 : W := mkw 0x04d6c00014d45000 0x009ad800029a8a00 0xf8fec00010fe7805 0xbf1fd800021fcf00

def z262 : W := mkw 0x020b000012050000 0x004160000240a000 0x570e000017000000 0x2ae1c00002e00000

def z263 : W := mkw 0x0490000004900000 0x0092000000920000 0xbff1c0001ffff805 0xf7fe380003ffff00

def z264 : W := mkw 0x0966bb7dd06662ee 0x412cd76fba0ccc5d 0xf8eebffff0e667ff 0xbf1dd7fffe1cccff

def z265 : W := mkw 0x000004c2280a8e15 0x20000098450151c2 0x80114dc6681f9e07 0x500229b8cd03f3c0

def z266 : W := mkw 0x00000442a802ae0d 0x20000088550055c1 0x8001cc47e807fe07 0x50003988fd00ffc0

def z267 : W := mkw 0x0000048008080410 0x0000009001010082 0x88100f800818063e 0xd10201f0010300c7

def z268 : W := mkw 0x200004c2adbaafbd 0x2400009855b755f7 0x180000001ffffffc 0x0300000003ffffff

def z269 : W := mkw 0x0effd259906662ee 0x41dffa4b320ccc5d 0xfffff27990e667ff 0xfffffe4f321cccff

def z270 : W := mkw 0x27b97f800fb915b0 0x04f72ff001f722b6 0xbff17f801ff99ffe 0xf7fe2ff003ff33ff

def z271 : W := mkw 0x2df6bfdbbdfeefff 0x65bed7fb77bfddff 0xffffffffffffffff 0xffffffffffffffff

def z272 : W := mkw 0x00201200002000a0 0x0004024000040014 0x00003200000007fa 0x00000640000000ff

def z273 : W := mkw 0x07fdfb3544d05000 0x00ffbf66a89a0a00 0xefffffffe0f87803 0xfdfffffffc1f0f00

def z274 : W := mkw 0x0000048008080410 0x0000009001010082 0x00100d8008180000 0x400201b001030000

def z275 : W := mkw 0x05b03fc2a80aae1d 0x20b607f8550155c3 0xaff1ffc7e81ffe3f 0xf5fe3ff8fd03ffc7

def z276 : W := mkw 0x27dfed801fdd5510 0x04fbfdb003fbaaa2 0xffffcd801ffff805 0xfffff9b003ffff00

def z277 : W := mkw 0x04d4c00004d05000 0x009a9800009a0a00 0x20e0000000e00000 0x041c0000001c0000

def z278 : W := mkw 0x06dfc00016d55000 0x00dbf80002daaa00 0x68ffc00000fff801 0x8d1ff800001fff00

def z279 : W := mkw 0x0209402440000000 0x0041280488000000 0x0001400660000000 0x00002800cc000000

def z280 : W := mkw 0x086496d3a86aeebd 0x610c92da750d5dd7 0xa8f1cfc7e8fffe3f 0xd51e39f8fd1fffc7

def z281 : W := mkw 0x17dfe82c17d55142 0x82fbfd0582faaa28 0xfffff0381ffff9c5 0xfffffe0703ffff38

def z282 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000fc7e0000002 0x000001f8fc000000

def z283 : W := mkw 0x0020121100000000 0x0004024220000000 0x0000327980000002 0x0000064f30000000

def z284 : W := mkw 0x08649291a06868b8 0x610c9252340d0d17 0x28f0c381e0f87838 0x851e18703c1f0f07

def z285 : W := mkw 0x000000408002220c 0x0000000810004441 0x8811c241881ffe3f 0xd10238483103ffc7

def z286 : W := mkw 0x0cf6d359d06662ee 0x419eda6b3a0ccc5d 0xf8fef3f9f0e667ff 0xbf1fde7f3e1cccff

def z287 : W := mkw 0x03092c2409000500 0x00612584812000a0 0xd70f3c7e1f0007c7 0x7ae1e78fc3e000f8

def z288 : W := mkw 0x07996de6e80aae1d 0x20f32dbcdd0155c3 0x8f11cfc7e81ffe3f 0xd1e239f8fd03ffc7

def z289 : W := mkw 0x2df4bf918df865b8 0x45be97f231bf0cb7 0xbff0bf819ff867fe 0xf7fe17f033ff0cff

def z290 : W := mkw 0x08669259906662ee 0x410cd24b320ccc5d 0x70ee327990e007fa 0x2e1dc64f321c00ff

def z291 : W := mkw 0x0490000004900000 0x0092000000920000 0x28f0000000f80000 0x851e0000001f0000

def z292 : W := mkw 0x132b3e6e1b2787e7 0x826567cdc364f0fc 0xffef3e7e1fe787ff 0xfffde7cfc3fcf0ff

def z293 : W := mkw 0x25902d800db805b0 0x04b205b001b700b6 0x1f100d801ff807fc 0x43e201b003ff00ff

def z294 : W := mkw 0x06dfc4823edddc11 0x20dbf89047dbbb82 0xffffcd867ffff805 0xfffff9b0cfffff00

def z295 : W := mkw 0x0000000000000000 0x0000000000000000 0x0810c00000187800 0x8102180000030f00

def z296 : W := mkw 0x1b0b2c6e9b67e7ef 0xc361658dd36cfcfd 0xdf0f3c7e1fe7e7ff 0x7be1e78fc3fcfcff

def z297 : W := mkw 0x120b006e12078247 0x8241600dc240f048 0xd00f307e100787c7 0x3a01e60fc200f0f8

def z298 : W := mkw 0x0699400006911000 0x00d3280000d22200 0x0700000007000000 0x00e0000000e00000

def z299 : W := mkw 0x25b03f000db005a0 0x04b607e001b600b4 0xb7e03c001fe007c6 0x76fc078003fc00f8

def z300 : W := mkw 0x130b2c2c1b050542 0x826165858360a0a8 0xd70e3c381f0007c6 0x7ae1c78703e000f8

def z301 : W := mkw 0x26dfc4801ffd55b0 0x04dbf89003ffaab6 0xffffc0001ffffffd 0xfffff80003ffffff

def z302 : W := mkw 0x08669259906662ee 0x410cd24b320ccc5d 0x68ee827980e66039 0x8d1dd04f301ccc07

def z303 : W := mkw 0x08669259106642e6 0x410cd24b220cc85c 0xf0ee307810e607c7 0x3e1dc60f021cc0f8

def z304 : W := mkw 0x00000080a0082818 0x2000001014010503 0x0800000000187838 0x0100000000030f07

def z305 : W := mkw 0x0cf4d21184f070a8 0x419e9a42309e0e15 0x28f0c20180f87838 0x851e1840301f0f07

def z306 : W := mkw 0x04f4d7d3e80aae1d 0x209e9afa7d0155c3 0xa8f1cfc7e81ffe3f 0xd51e39f8fd03ffc7

def z307 : W := mkw 0x08649211806060a8 0x410c9242300c0c15 0xb8e0b20190e067fe 0xb71c1640321c0cff

def z308 : W := mkw 0x2ffffffdddfe67fe 0x45ffffffbbbfccff 0xfffffffffffe67ff 0xffffffffffffccff

def z309 : W := mkw 0x0002000016d55000 0x0000400002daaa00 0x1000000017e00000 0x0200000002fc0000

def z310 : W := mkw 0x0000000000000000 0x0000000000000000 0x8800800000066005 0x910010000000cc00

def z311 : W := mkw 0x25902d800d980510 0x04b205b001b300a2 0xbff00d801ff80004 0xf7fe01b003ff0000

def z312 : W := mkw 0x06dfc4421ed7d605 0x00dbf88843dafac0 0xffffcc461ffffe07 0xfffff988c3ffffc0

def z313 : W := mkw 0x24f4d38004f850b0 0x049e9a70009f0a16 0x28f0c38000f87838 0x851e1870001f0f07

def z314 : W := mkw 0x25b03f800db805b0 0x04b607f001b700b6 0xbff1ffc7fff807ff 0xf7fe3ff8ffff00ff

def z315 : W := mkw 0x07996da668088c11 0x20f32db4cd011182 0x07114d8668199800 0x40e229b0cd033300

def z316 : W := mkw 0x08669259906662ee 0x410cd24b320ccc5d 0x70eeb07990e661c1 0x2e1dd60f321ccc38

def z317 : W := mkw 0x13092c660b038705 0x8261258cc16070e0 0x87010c460f078607 0x50e02188c1e0f0c0

def z318 : W := mkw 0x0044c01140000000 0x0008980228000000 0x0000c001e0000000 0x000018003c000000

def z319 : W := mkw 0x0a6fd27dd06662ee 0x414dfa4fba0ccc5d 0xf8eff27ff0e667ff 0xbf1dfe4ffe1cccff

def z320 : W := mkw 0x06dfc00016d55000 0x00dbf80002daaa00 0x471fc0000f1ff801 0x48e3f80001e3ff00

def z321 : W := mkw 0x1002044a1fd7d747 0x8200408943fafae8 0x180000001fffffc4 0x0300000003fffff8

def z322 : W := mkw 0x07fdffb548080410 0x00ffbff6a9010082 0xefffffffe818063f 0xfdfffffffd0300c7

def z323 : W := mkw 0x080000598002224e 0x4100000b30004449 0x0000007980000000 0x0000000f30000000

def z324 : W := mkw 0x27bb3f801fbd05b0 0x04f767f003f7a0b6 0xffff3f801fff87ff 0xffffe7f003fff0ff

def z325 : W := mkw 0x034de83540000000 0x0069bd06a8000000 0xc70ffc7fe0000003 0x78e1ff8ffc000000

def z326 : W := mkw 0x130b2cee1b0f8757 0x8261659dc361f0ea 0xdf1f3ffe1f1f87ff 0xfbe3e7ffc3e3f0ff

def z327 : W := mkw 0x0020131140000000 0x0004026228000000 0x00000381e0000000 0x000000703c000000

def z328 : W := mkw 0x07fffb3552455000 0x00ffff66aa48aa00 0xe7ffffffe007f803 0xfcfffffffc00ff00

def z329 : W := mkw 0x0002000012050000 0x000040000240a000 0x100000001f078004 0x0200000003e0f000

def z330 : W := mkw 0x136fbe7f1b078747 0x826df7cfe360f0e8 0xf7efbe7f9f0787c7 0xfefdf7cff3e0f0f8

def z331 : W := mkw 0x0490000004900000 0x0092000000920000 0x071000000f180000 0x40e2000001e30000

def z332 : W := mkw 0x25b03f800db805b0 0x04b607f001b700b6 0x37e03f8017e007fa 0x26fc07f002fc00ff

def z333 : W := mkw 0x130b286e13078347 0x8261650dc260f068 0x570f307e170781c1 0x2ae1e60fc2e0f038

def z334 : W := mkw 0x08201211802020a8 0x4104024230040415 0x0000020180000038 0x0000004030000007

def z335 : W := mkw 0x16dfc06e16d7d247 0x82dbf80dc2dafa48 0xffffc07e1ffff805 0xfffff80fc3ffff00

def z336 : W := mkw 0x08201259802222ee 0x4104024b3004445d 0xb8e0327990e007fe 0xb71c064f321c00ff

def z337 : W := mkw 0x069b400016951000 0x00d3680002d2a200 0xd71f40001f1f9805 0x7ae3e80003e3f300

def z338 : W := mkw 0x07fdfb3540000000 0x00ffbf66a8000000 0x67ee3fffe0000002 0x2cfdc7fffc000000

def z339 : W := mkw 0x07fdffb768088c11 0x20ffbff6ed011182 0xe7ffffffe8199803 0xfcfffffffd033300

def z340 : W := mkw 0x030b282412050000 0x006165048240a000 0xd70f3c7e1f078007 0x7ae1e78fc3e0f000

def z341 : W := mkw 0x080204cab86eeeff 0x61004099570ddddf 0x9811cfc7f8ffffff 0xd30239f8ff1fffff

def z342 : W := mkw 0x0866965b9866e6ef 0x410cd2cb730cdcdd 0xf8efbe7f98e7e7ff 0xff1df7cff31cfcff

def z343 : W := mkw 0x0a6fd259926772ee 0x414dfa4b324cee5d 0xf8eff27990e7ffff 0xbf1dfe4f321cffff

def z344 : W := mkw 0x000004c2a80aae1d 0x20000098550155c3 0x08114d86681ffe3c 0x410229b0cd03ffc7

def z345 : W := mkw 0x000000c2a00aaa1d 0x2000001854015543 0x0811c3c7e01ff839 0x81023878fc03ff07

def z346 : W := mkw 0x000000408002220c 0x0000000810004441 0x000002418000063a 0x00000048300000c7

def z347 : W := mkw 0x084680599046624e 0x4108d00b3208cc49 0xc80e82798006663f 0x9901d04f3000ccc7

def z348 : W := mkw 0x0000004800020246 0x0000000900004048 0x00003078000007c2 0x0000060f000000f8

def z349 : W := mkw 0x020b04c2ba0fae1d 0x204160985741f5c3 0xdf1fcfc7ff1ffe3f 0xfbe3f9f8ffe3ffc7

def z350 : W := mkw 0x020b04421a078605 0x004160884340f0c0 0xd70f0c461f078607 0x7ae1e188c3e0f0c0

def z351 : W := mkw 0x17dfec6e1fd7d747 0x82fbfd8dc3fafae8 0xf7ef3c7e1fe787c7 0x7efde78fc3fcf0f8

def z352 : W := mkw 0x06dfc00016d55000 0x00dbf80002daaa00 0x77ff40001ff99800 0x6effe80003ff3300

def z353 : W := mkw 0x086692599046624e 0x410cd24b3208cc49 0xe0eeb27980066003 0xbc1dd64f3000cc00

def z354 : W := mkw 0x08468048906662ee 0x4108d009120ccc5d 0xf8ee800010e667fd 0xbf1dd000021cccff

def z355 : W := mkw 0x25b03b0005b001a0 0x04b6076000b60034 0xbff030001ff801c4 0xf7fe060003ff0038

def z356 : W := mkw 0x000004c2a80aae1d 0x20000098550155c3 0x88008241881ffe3f 0x910010483103ffc7

def z357 : W := mkw 0x2cf693d994fe62fe 0x459ed27b329fcc5f 0xf8feb3f990fe67ff 0xbf1fd67f321fccff

def z358 : W := mkw 0x020b000016d55000 0x0041600002daaa00 0xdf0f00001ffff805 0x7be1e00003ffff00

def z359 : W := mkw 0x000200489006224e 0x000040091200c449 0xd80eb279900667ff 0xbb01d64f3200ccff

def z360 : W := mkw 0x0002000012455000 0x000040000248aa00 0x000000000007f800 0x000000000000ff00

def z361 : W := mkw 0x036dfb3540000000 0x006dbf66a8000000 0x400fffffe0000003 0x0801fffffc000000

def z362 : W := mkw 0x00000080a0082818 0x2000001014010503 0x8811cfc7e018783b 0xd10239f8fc030f07

def z363 : W := mkw 0x00000000a0002808 0x2000000014000501 0x0000c001e0007800 0x000018003c000f00

def z364 : W := mkw 0x25902d800d980510 0x04b205b001b300a2 0x8f100f800f18063e 0xd1e201f001e300c7

def z365 : W := mkw 0x300204ca1fbf87f7 0x8600409943f7f0fe 0x180000001fff87fc 0x0300000003fff0ff

def z366 : W := mkw 0x006492518002220c 0x000c924a30004441 0xe8eeb2798006663f 0xbd1dd64f3000ccc7

def z367 : W := mkw 0x000004c2a80aae1d 0x20000098550155c3 0x0801c047e81ffe3d 0x01003808fd03ffc7

def z368 : W := mkw 0x04f4d31140000000 0x009e9a6228000000 0xe0fef3f9e0000003 0xbc1fde7f3c000000

def z369 : W := mkw 0x024fc4c2ba4ffe1d 0x2049f8985749ffc3 0xc81fcfc7e81ffe3f 0xd903f9f8fd03ffc7

def z370 : W := mkw 0x05f4fb1140000000 0x00be9f6228000000 0xa7f0ff81e0000002 0xf4fe1ff03c000000

def z371 : W := mkw 0x2590290005900100 0x04b2052000b20020 0x0700000007000000 0x00e0000000e00000

def z372 : W := mkw 0x0000048008080410 0x0000009001010082 0x00000f800000063a 0x000001f0000000c7

def z373 : W := mkw 0x00201240802222ac 0x0004024810044455 0xb8e0b24190e667ff 0xb71c1648321cccff

def z374 : W := mkw 0x000004c2a80aae1d 0x20000098550155c3 0x0810cfc7e0187e3a 0x810219f8fc030fc7

def z375 : W := mkw 0x11203f7f49028747 0x822407efe92050e8 0x00003fffe00007c2 0x000007fffc0000f8

def z376 : W := mkw 0x0000000000000000 0x0000000000000000 0x80100f8000000002 0xd00201f000000000

def z377 : W := mkw 0x0846805bb046ea4f 0x6108d00b7608dd49 0x400fc07fe007f801 0x0801f80ffc00ff00

def z378 : W := mkw 0x08221259906662ee 0x4104424b320ccc5d 0x1800327990e667fe 0x0300064f321cccff

def z379 : W := mkw 0x11022c6e1b078747 0x8220458dc360f0e8 0x10003c7e1f0787c6 0x0200078fc3e0f0f8

def z380 : W := mkw 0x179b6c6e1f979747 0x82f36d8dc3f2f2e8 0xd71f7c7e1f1f9fc7 0x7ae3ef8fc3e3f3f8

def z381 : W := mkw 0x25f4ff914db805b0 0x04be9ff229b700b6 0xbff0ff81fff807fe 0xf7fe1ff03fff00ff

def z382 : W := mkw 0x17dfeceebfdfff5f 0xa2fbfd9dd7fbffeb 0xffffffffffffffff 0xffffffffffffffff

def z383 : W := mkw 0x069944c2ae9bbe1d 0x20d3289855d377c3 0x8f11cfc7ef1ffe3f 0xd1e239f8fde3ffc7

def z384 : W := mkw 0x17fdff7f49028747 0x82ffbfefe92050e8 0xe7ffffffe00007c3 0xfcfffffffc0000f8

def z385 : W := mkw 0x25902d800d980510 0x04b205b001b300a2 0x97103d801f1807c6 0x72e207b003e300f8

def z386 : W := mkw 0x06ddc00000000000 0x00dbb80000000000 0xe7ffcfc7e0000003 0xfcfff9f8fc000000

def z387 : W := mkw 0x0000000000000000 0x0000000000000000 0x00114d8660000000 0x400229b0cc000000

def z388 : W := mkw 0x08649251806262ac 0x410c924a300c4c55 0xa8e0824180e6663f 0x951c1048301cccc7

def z389 : W := mkw 0x0802004896f772ee 0x4100400912deee5d 0x180000001ffffffc 0x0300000003ffffff

def z390 : W := mkw 0x25b03f822db88db1 0x24b607f045b711b6 0xbff17f867ff99ffe 0xf7fe2ff0cfff33ff

def z391 : W := mkw 0x0000004200028205 0x0000000840005040 0x0001004600078001 0x00002008c000f000

def z392 : W := mkw 0x000004c2a80aae1d 0x20000098550155c3 0x88008fc7e006663f 0x910011f8fc00ccc7

def z393 : W := mkw 0x07fdfb3540000000 0x00ffbf66a8000000 0xe7fff03800000001 0xfcfffe0700000000

def z394 : W := mkw 0x25b03b8005b801b0 0x04b6077000b70036 0x3ff0338017f801f8 0xa7fe067002ff003f

def z395 : W := mkw 0x000204c2bedffe1d 0x2000409857dbffc3 0x9811cfc7fffffe3f 0xd30239f8ffffffc7

def z396 : W := mkw 0x0000048228088c11 0x2000009045011182 0x8811cd86681ff805 0xd10239b0cd03ff00

def z397 : W := mkw 0x01002c0009000500 0x00200580012000a0 0x07000c000f000000 0x40e0018001e00000

def z398 : W := mkw 0x2490018004980010 0x0492003000930002 0x0010018000180000 0x0002003000030000

def z399 : W := mkw 0x27fdfbb544b800b0 0x04ffbf76a8970016 0xefffffffe0f8003b 0xfdfffffffc1f0007

def z400 : W := mkw 0x07b97b3540000000 0x00f72f66a8000000 0x07117fffe0000002 0x40e22ffffc000000

def z401 : W := mkw 0x332b3fee1b2f87f7 0x866567fdc365f0fe 0xd70f3ffe1f0787ff 0x7ae1e7ffc3e0f0ff

def z402 : W := mkw 0x0590290000000000 0x00b2052000000000 0x07100d8000000000 0x40e201b000000000

def z403 : W := mkw 0x2cf4939184f860b8 0x459e9272309f0c17 0x28f0838180f86038 0x851e1070301f0c07

def z404 : W := mkw 0x0000048228088c11 0x2000009045011182 0x88114f8668199e3e 0xd10229f0cd0333c7

def z405 : W := mkw 0x0000000000000000 0x0000000000000000 0x80010c4600000003 0x50002188c0000000

def z406 : W := mkw 0x07fdff7748028605 0x00ffbfeee90050c0 0xe7ffffffe8078607 0xfcfffffffd00f0c0

def z407 : W := mkw 0x1002000813050142 0x820040010260a028 0x10000000170001c0 0x0200000002e00038

def z408 : W := mkw 0x134fec7f5b078747 0x8269fd8feb60f0e8 0xd70ffc7fff0787c7 0x7ae1ff8fffe0f0f8

def z409 : W := mkw 0x1100282c01000142 0x8220050580200028 0x00003038000001c0 0x0000060700000038

def z410 : W := mkw 0x11002ceea90aaf5f 0xa220059dd52155eb 0x00003fffe00007fa 0x000007fffc0000ff

def z411 : W := mkw 0x06dfc00016d55000 0x00dbf80002daaa00 0xf7ef00001fe78005 0x7efde00003fcf000

def z412 : W := mkw 0x120b046e1a078647 0x8241608dc340f0c8 0xc00f0c7e08078607 0x5801e18fc100f0c0

def z413 : W := mkw 0x024fc00012455000 0x0049f8000248aa00 0xc81fc000081ff805 0xd903f8000103ff00

def z414 : W := mkw 0x330b2cee1fbf87f7 0x8661659dc3f7f0fe 0xdf0f3c7e1fff87ff 0x7be1e78fc3fff0ff

def z415 : W := mkw 0x1802044a9b67e7ef 0xc3004089536cfcfd 0x180000001fe7e7fc 0x0300000003fcfcff

def z416 : W := mkw 0x11002c2609008501 0x82200584c12010a0 0x00000c0600000000 0x00000180c0000000

def z417 : W := mkw 0x0000044208028605 0x00000088410050c0 0x00000c4600000602 0x00000188c00000c0

def z418 : W := mkw 0x08221248906662ee 0x41044249120ccc5d 0xb8e0320010e667fe 0xb71c0640021cccff

def z419 : W := mkw 0x06dfc00016d55000 0x00dbf80002daaa00 0xf7ffc00017e00001 0xfefff80002fc0000

def z420 : W := mkw 0x17dfe82c17d55142 0x82fbfd0582faaa28 0x77ee303817e001c0 0x2efdc60702fc0038

def z421 : W := mkw 0x01203b3540000000 0x00240766a8000000 0x8011ffffe0000003 0xd0023ffffc000000

def z422 : W := mkw 0x17996d264b018501 0x82f32da4c96030a0 0x07114d866f018000 0x40e229b0cde03000

def z423 : W := mkw 0x130b286e12078247 0x8261650dc240f048 0xc70f3c7e00078003 0x78e1e78fc000f000

def z424 : W := mkw 0x13092ca62b098d11 0xa2612594c56131a2 0x07114d866f199800 0x40e229b0cde33300

def z425 : W := mkw 0x100204cabb0faf5f 0xa20040995761f5eb 0x9811cfc7ff1fffff 0xd30239f8ffe3ffff

def z426 : W := mkw 0x01022c4819060746 0x002045890320c0e8 0xd70e3c781f0607c7 0x7ae1c78f03e0c0f8

def z427 : W := mkw 0x0699400006911000 0x00d3280000d22200 0x8f11c0000f1ff805 0xd1e2380001e3ff00

def z428 : W := mkw 0x11002ceea90aaf5f 0xa220059dd52155eb 0x8811ffffe81fffff 0xd1023ffffd03ffff

def z429 : W := mkw 0x06dfc00010444000 0x00dbf80002088800 0xffffc00010e66005 0xfffff800021ccc00

def z430 : W := mkw 0x24b01380a4b828b8 0x2496027014970517 0x28f0c381e0f87838 0x851e18703c1f0f07

def z431 : W := mkw 0x25f4ff800df855b0 0x04be9ff001bf0ab6 0xbff0ff801ff87ffe 0xf7fe1ff003ff0fff

def z432 : W := mkw 0x0000000000000000 0x0000000000000000 0x90003000100007c6 0x32000600020000f8

def z433 : W := mkw 0x01203e00092005a0 0x002407c0012400b4 0xbfe03e001fe007fe 0xf7fc07c003fc00ff

def z434 : W := mkw 0x08201219002000e2 0x410402432004001c 0x00003038000001c0 0x0000060700000038

def z435 : W := mkw 0x06fdd21100000000 0x00dfba4220000000 0xe7fff27980000003 0xfcfffe4f30000000

def z436 : W := mkw 0x0164bb3540000000 0x002c9766a8000000 0xe0eebfffe0000003 0xbc1dd7fffc000000

def z437 : W := mkw 0x25f4bf910db805b0 0x04be97f221b700b6 0xfffebff99ff807ff 0xffffd7ff33ff00ff

def z438 : W := mkw 0x0100280000000000 0x0020050000000000 0x87003c0000000002 0x70e0078000000000

def z439 : W := mkw 0x06ddc00006d15000 0x00dbb80000da2a00 0x2ff1c0000ff9f800 0xc5fe380001ff3f00

def z440 : W := mkw 0x25b03b0005b001a0 0x04b6076000b60034 0xb7f03f8017e001c2 0xf6fe07f002fc0038

def z441 : W := mkw 0x0002000016d55000 0x0000400002daaa00 0x9811c0001ffff805 0xd302380003ffff00

def z442 : W := mkw 0x0effd21196f570a8 0x41dffa4232deae15 0xffffc2019ffff83d 0xfffff84033ffff07

def z443 : W := mkw 0x27fdffb5492805b0 0x04ffbff6a92500b6 0xe7ffffffe00007fb 0xfcfffffffc0000ff

def z444 : W := mkw 0x08649259802222ee 0x410c924b3004445d 0xe0eeb279800007fb 0xbc1dd64f300000ff

def z445 : W := mkw 0x1b2b3e7f9b27a7ef 0xc36567cff364f4fd 0xd70f3e7f9f0787ff 0x7ae1e7cff3e0f0ff

def z446 : W := mkw 0x24b0138004b800b0 0x0496027000970016 0xbff003801ff8003c 0xf7fe007003ff0007

def z447 : W := mkw 0x134fec6e1b47d747 0x8269fd8dc368fae8 0xd70ffc7e1f07ffc7 0x7ae1ff8fc3e0fff8

def z448 : W := mkw 0x06dfc00012050000 0x00dbf8000240a000 0xf7ffc0001f078005 0xfefff80003e0f000

def z449 : W := mkw 0x21203fb5492805b0 0x042407f6a92500b6 0x00003fffe00007fa 0x000007fffc0000ff

def z450 : W := mkw 0x07dfec001fd55500 0x00fbfd8003faaaa0 0xfffffc001fffffc7 0xffffff8003fffff8

def z451 : W := mkw 0x08669219106440e2 0x410cd243220c881c 0xf8eeb03810e661c5 0xbf1dd607021ccc38

def z452 : W := mkw 0x27fdfb3545b001a0 0x04ffbf66a8b60034 0xf7fffffff7e001c3 0xfefffffffefc0038

def z453 : W := mkw 0x2df6bb5995f663ee 0x45bed76b32becc7d 0xffeeb27997e667ff 0xbffdd64f32fcccff

def z454 : W := mkw 0x20000480092805b0 0x04000090012500b6 0x00000000000007f8 0x00000000000000ff

def z455 : W := mkw 0x0044c00000405000 0x0008980000080a00 0x0000c00000007800 0x0000180000000f00

def z456 : W := mkw 0x0cf6925994f662ee 0x419ed24b329ecc5d 0xfffeb2799ffe67ff 0xffffd64f33ffccff

def z457 : W := mkw 0x0064921100000000 0x000c924220000000 0x20e0820180000000 0x841c104030000000

def z458 : W := mkw 0x0046800016d55000 0x0008d00002daaa00 0xf8ee80001ffff805 0xbf1dd00003ffff00

def z459 : W := mkw 0x06ffd20016f550a0 0x00dffa4002deaa14 0xfffff2001fffffff 0xfffffe4003ffffff

def z460 : W := mkw 0x07fffb3556d55000 0x00ffff66aadaaa00 0xf7fffffff7e00003 0xfefffffffefc0000

def z461 : W := mkw 0x00201680082804b0 0x000402d001050096 0xb8f03f8018f807fe 0xf71e07f0031f00ff

def z462 : W := mkw 0x0000000000000000 0x0000000000000000 0xb8e0000010e00004 0xb71c0000021c0000

def z463 : W := mkw 0x086696dbb86eeeff 0x610cd2db770ddddf 0xf8eeb27998ffffff 0xbf1dd64f331fffff

def z464 : W := mkw 0x13092c6e09028747 0x8261258dc12050e8 0xc70f3c7e000007c3 0x78e1e78fc00000f8

def z465 : W := mkw 0x004680409046620c 0x0008d0081208cc41 0xf8ee824190e6663f 0xbf1dd048321cccc7

def z466 : W := mkw 0x024f800012454000 0x0049f0000248a800 0xffef80001fe7e005 0xfffdf00003fcfc00

def z467 : W := mkw 0x036dba3500000000 0x006db746a0000000 0xe7efbe7f80000003 0xfcfdf7cff0000000

def z468 : W := mkw 0x05b03b00002000a0 0x00b6076000040014 0xbff03f8010e007fe 0xf7fe07f0021c00ff

def z469 : W := mkw 0x21203f80092805b0 0x042407f0012500b6 0x88103f80081807fe 0xd10207f0010300ff

def z470 : W := mkw 0x06dfc042b6d7fa0d 0x20dbf80856daff41 0xffffc047fffff805 0xfffff808ffffff00

def z471 : W := mkw 0x130b282c13050142 0x826165058260a028 0xd70f30381f0781c5 0x7ae1e60703e0f038

def z472 : W := mkw 0x0064921100000000 0x000c924220000000 0x60ee303800000000 0x2c1dc60700000000

def z473 : W := mkw 0x0ffffb7dd06662ee 0x41ffff6fba0ccc5d 0xffeeb27990e667ff 0xbffdd64f321cccff

def z474 : W := mkw 0x0cf4d311c06060a8 0x419e9a62380c0c15 0x28f0c381e0e06038 0x851e18703c1c0c07

def z475 : W := mkw 0x06dfc00012455000 0x00dbf8000248aa00 0xe7ffc0000007f801 0xfcfff8000000ff00

def z476 : W := mkw 0x08468059906662ee 0x4108d00b320ccc5d 0x580e807990e667fd 0x0b01d00f321cccff

def z477 : W := mkw 0x21203b00012001a0 0x0424076000240034 0x00003000000001c0 0x0000060000000038

def z478 : W := mkw 0x130b2c6e1b078747 0x8261658dc360f0e8 0x570e30381f0787c4 0x2ae1c60703e0f0f8

def z479 : W := mkw 0x05b03b3540000000 0x00b60766a8000000 0xa7f03fffe0000002 0xf4fe07fffc000000

def z480 : W := mkw 0x06ffd21116d55000 0x00dffa4222daaa00 0xfffff2799ffff807 0xfffffe4f33ffff00

def z481 : W := mkw 0x0309282400000000 0x0061250480000000 0x470e303800000000 0x28e1c60700000000

def z482 : W := mkw 0x200004800d980510 0x0400009001b300a2 0x000000000f180000 0x0000000001e30000

def z483 : W := mkw 0x25b03fc08dba27bc 0x04b607f811b744f7 0xbff0bfc19ffe67ff 0xf7fe17f833ffccff

def z484 : W := mkw 0x0209400002011000 0x0041280000402200 0x0001400000019800 0x0000280000003300

def z485 : W := mkw 0x00000080a0082818 0x2000001014010503 0x8811c381e81ff83d 0xd10238703d03ff07

def z486 : W := mkw 0x0066925910060246 0x000cd24b2200c048 0xf0eeb279900607c7 0xbe1dd64f3200c0f8

def z487 : W := mkw 0x05b03f0009000500 0x00b607e0012000a0 0xb7f03f801f0007c6 0xf6fe07f003e000f8

def z488 : W := mkw 0x21002c800db805b0 0x0420059001b700b6 0x9f003c001ff807fe 0x73e0078003ff00ff

def z489 : W := mkw 0x1209002602018001 0x82412004c0403000 0x0001000600018000 0x00002000c0003000

def z490 : W := mkw 0x08669259906662ee 0x410cd24b320ccc5d 0x400eb279800667fb 0x0801d64f3000ccff

def z491 : W := mkw 0x069944822e999c11 0x20d3289045d33382 0x07114d866f199800 0x40e229b0cde33300

def z492 : W := mkw 0x27b97fa44db805b0 0x04f72ff489b700b6 0xbff17f867ff807fe 0xf7fe2ff0cfff00ff

def z493 : W := mkw 0x120b046e1b078747 0x8241608dc360f0e8 0x500f007e1f0787c5 0x0a01e00fc3e0f0f8

def z494 : W := mkw 0x07fffb3556d55000 0x00ffff66aadaaa00 0x77ee303817e00000 0x2efdc60702fc0000

def z495 : W := mkw 0x25f6bf801dfc45b0 0x04bed7f003bf88b6 0xfffebf801ffe67ff 0xffffd7f003ffccff

def z496 : W := mkw 0x07fffb3552050000 0x00ffff66aa40a000 0xf7ffffffff078007 0xfeffffffffe0f000

def z497 : W := mkw 0x000004c2a80aae1d 0x20000098550155c3 0x0810c381e81ffe3c 0x810218703d03ffc7

def z498 : W := mkw 0x2000008004b800b0 0x0400001000970016 0x0800000000f80038 0x01000000001f0007

def z499 : W := mkw 0x000000408002220c 0x0000000810004441 0x0000804180066001 0x000010083000cc00

def z500 : W := mkw 0x04f4d31140000000 0x009e9a6228000000 0xa0f1cfc7e0000003 0xd41e39f8fc000000

def z501 : W := mkw 0x08000048802222ee 0x410000091004445d 0x00000000000007f8 0x00000000000000ff

def z502 : W := mkw 0x0ffffb7dd046624e 0x41ffff6fba08cc49 0xe7ffffffe0066003 0xfcfffffffc00cc00

def z503 : W := mkw 0x200004c2adbaafbd 0x2400009855b755f7 0x9811cfc7ffffffff 0xd30239f8ffffffff

def z504 : W := mkw 0x06dfc4c2bedffe1d 0x20dbf89857dbffc3 0xffffc0001ffffe3d 0xfffff80003ffffc7

def z505 : W := mkw 0x0effd6dbbefffeff 0x61dffadb77dfffdf 0xffffffffffffffff 0xffffffffffffffff

def z506 : W := mkw 0x0209000000000000 0x0041200000000000 0xc70f000000000001 0x78e1e00000000000

def z507 : W := mkw 0x24b017800db805b0 0x049602f001b700b6 0x38f003801ff807fc 0x871e007003ff00ff

def z508 : W := mkw 0x024fc00016d55000 0x0049f80002daaa00 0x580fc0001ffff805 0x0b01f80003ffff00

def z509 : W := mkw 0x0000000000000000 0x0000000000000000 0x0011400008199800 0x4002280001033300

def z510 : W := mkw 0x1002044a1b078747 0x820040894360f0e8 0x90010c461f0787c7 0x52002188c3e0f0f8

def z511 : W := mkw 0x00000480a8082c18 0x2000009015010583 0x8810cf81e8187e3e 0xd10219f03d030fc7

def z512 : W := mkw 0x11002c6e09028747 0x8220058dc12050e8 0x80013c7e080787c7 0x5000278fc100f0f8

def z513 : W := mkw 0x024dc03540000000 0x0049b806a8000000 0x400e003800000000 0x0801c00700000000

def z514 : W := mkw 0x1b6fba7d936763ee 0xc36df74fb26cec7d 0xffeeb27997e667ff 0xbffdd64f32fcccff

def z515 : W := mkw 0x0490410040000000 0x0092082008000000 0x0010418060000000 0x000208300c000000

def z516 : W := mkw 0x07dde92440000000 0x00fbbd2488000000 0xe7ffcd8660000001 0xfcfff9b0cc000000

def z517 : W := mkw 0x2db23fc89dfe67fe 0x45b647f913bfccff 0xbff03f801ffe67fe 0xf7fe07f003ffccff

def z518 : W := mkw 0x280204c89dfe67fe 0x4500409913bfccff 0x180000001ffe67fc 0x0300000003ffccff

def z519 : W := mkw 0x24b017c2acbaaebd 0x249602f8559755d7 0xa8f1cfc7e8fffe3f 0xd51e39f8fd1fffc7

def z520 : W := mkw 0x08669259906662ee 0x410cd24b320ccc5d 0xf8fffffff0e667ff 0xff1ffffffe1cccff

def z521 : W := mkw 0x1fffff7fdb67e7ef 0xc3ffffeffb6cfcfd 0xffffffffffe7e7ff 0xfffffffffffcfcff

def z522 : W := mkw 0x08649211806060a8 0x410c9242300c0c15 0xe8eeb27980e0603b 0xbd1dd64f301c0c07

def z523 : W := mkw 0x35b23fca1fbf87f7 0x86b647f943f7f0fe 0xbff03f801fff87fe 0xf7fe07f003fff0ff

def z524 : W := mkw 0x0edfc04896f772ee 0x41dbf80912deee5d 0xffffc0001ffffffd 0xfffff80003ffffff

def z525 : W := mkw 0x27fdfb3545b001a0 0x04ffbf66a8b60034 0x77ee303817e001c0 0x2efdc60702fc0038

def z526 : W := mkw 0x084680599046624e 0x4108d00b3208cc49 0xd00eb079900667c7 0x3a01d60f3200ccf8

def z527 : W := mkw 0x0000000000000000 0x0000000000000000 0x8001000008078005 0x500020000100f000

def z528 : W := mkw 0x37bb3fac1fbd05f2 0x86f767f583f7a0be 0xfffe3fb81ff807fe 0xffffc7f703ff00ff

def z529 : W := mkw 0x130b2c6e1fd7d747 0x8261658dc3fafae8 0xdf0f3c7e1fffffc7 0x7be1e78fc3fffff8

def z530 : W := mkw 0x00000042a002aa0d 0x2000000854005541 0x8811c047e81ff805 0xd1023808fd03ff00

def z531 : W := mkw 0x08669259906662ee 0x410cd24b320ccc5d 0x38e0820190e667fc 0x871c1040321cccff

def z532 : W := mkw 0x0866925996f772ee 0x410cd24b32deee5d 0xf8eeb2799fffffff 0xbf1dd64f33ffffff

def z533 : W := mkw 0x25b03f800db805b0 0x04b607f001b700b6 0x2ff00f800ff80038 0xc5fe01f001ff0007

def z534 : W := mkw 0x0490400004901000 0x0092080000920200 0x0010400000181800 0x0002080000030300

def z535 : W := mkw 0x130b2c6e1b078747 0x8261658dc360f0e8 0x17010c061f0787c4 0x42e02180c3e0f0f8

def z536 : W := mkw 0x06fdd33540000000 0x00dfba66a8000000 0x60ffc3ffe0000001 0x8c1ff87ffc000000

def z537 : W := mkw 0x0002000810040042 0x0000400102008008 0x500e3038100001c0 0x2a01c60702000038

def z538 : W := mkw 0x0100282400000000 0x0020050480000000 0x00003c7e00000002 0x0000078fc0000000

def z539 : W := mkw 0x0046800010444000 0x0008d00002088800 0x400e800000066001 0x0801d0000000cc00

def z540 : W := mkw 0x06ddc03540000000 0x00dbb806a8000000 0xe7ffc07fe0000001 0xfcfff80ffc000000

def z541 : W := mkw 0x07fffb0016d55000 0x00ffff6002daaa00 0xffffff801ffff807 0xfffffff003ffff00

def z542 : W := mkw 0x0000000000000000 0x0000000000000000 0x0010c381e0000000 0x800218703c000000

def z543 : W := mkw 0x27fdffb54db805b0 0x04ffbff6a9b700b6 0xfffe3fb81ff807fe 0xffffc7f703ff00ff

def z544 : W := mkw 0x0000000004900000 0x0000000000920000 0x180000001ff80004 0x0300000003ff0000

def z545 : W := mkw 0x124fc07f52078247 0x8249f80fea40f048 0x400fc07fe0078001 0x0801f80ffc00f000

def z546 : W := mkw 0x000004428802a60d 0x00000088510054c1 0x88018e478807e63f 0xd10031c8f100fcc7

def z547 : W := mkw 0x000004c2080a8615 0x00000098410150c2 0x88110fc6081f863f 0xd10221f8c103f0c7

def z548 : W := mkw 0x0000044208028605 0x00000088410050c0 0x0000000008078604 0x000000000100f0c0

def z549 : W := mkw 0x08020048906662ee 0x41004009120ccc5d 0x9800824190e667ff 0x93001048321cccff

def z550 : W := mkw 0x27b93fa40db805b0 0x04f727f481b700b6 0xffff3ffe1ff807ff 0xffffe7ffc3ff00ff

def z551 : W := mkw 0x286696d99dfe67fe 0x450cd2db33bfccff 0xf8eeb2799ffe67ff 0xbf1dd64f33ffccff

def z552 : W := mkw 0x07fffb3556d55000 0x00ffff66aadaaa00 0xfffff0381ffff805 0xfffffe0703ffff00

def z553 : W := mkw 0x0846801910444042 0x4108d00322088808 0x400e003800000000 0x0801c00700000000

def z554 : W := mkw 0x17996c260f919501 0x82f32d84c1f232a0 0x07114c060f199800 0x40e22980c1e33300

def z555 : W := mkw 0x07fdff3549000500 0x00ffbfe6a92000a0 0xf7ffffffff0007c7 0xfeffffffffe000f8

def z556 : W := mkw 0x01203ff7e80aae1d 0x202407fefd0155c3 0x00003fffe000063a 0x000007fffc0000c7

def z557 : W := mkw 0x25b03fc2adbaafbd 0x24b607f855b755f7 0xbff03f801ffffffe 0xf7fe07f003ffffff

def z558 : W := mkw 0x07fdfb0000000000 0x00ffbf6000000000 0xe7ffff8000000003 0xfcfffff000000000

def z559 : W := mkw 0x13092c260b018501 0x82612584c16030a0 0x97013c061f0187c6 0x72e02780c3e030f8

def z560 : W := mkw 0x25b03f800db805b0 0x04b607f001b700b6 0x37f03d801ff801c0 0x66fe07b003ff0038

def z561 : W := mkw 0x069b400016d55000 0x00d3680002daaa00 0x1f1140001ffff804 0x43e2280003ffff00

def z562 : W := mkw 0x024fc042b247fa0d 0x2049f8085648ff41 0x400fc047e007f801 0x0801f808fc00ff00

def z563 : W := mkw 0x086696dbb86eeeff 0x610cd2db770ddddf 0xf8eebffff0e667ff 0xbf1dd7fffe1cccff

def z564 : W := mkw 0x25b03fc2adbaafbd 0x24b607f855b755f7 0xbff03fc7fff807fe 0xf7fe07f8ffff00ff

def z565 : W := mkw 0x020b000012050000 0x004160000240a000 0xdf1fc0001f1ff805 0xfbe3f80003e3ff00

def z566 : W := mkw 0x130b2c261b058501 0x82616584c360b0a0 0xd70f0c061f078005 0x7ae1e180c3e0f000

def z567 : W := mkw 0x06ddc00000000000 0x00dbb80000000000 0x67ee000000000000 0x2cfdc00000000000

def z568 : W := mkw 0x0000000000000000 0x0000000000000000 0x970000001f000004 0x72e0000003e00000

def z569 : W := mkw 0x049004800c980410 0x0092009001930082 0xbff00f801ff8063e 0xf7fe01f003ff00c7

def z570 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000824180000003 0x9000104830000000

def z571 : W := mkw 0x0000040008000400 0x0000008001000080 0x80000c0008000606 0x50000180010000c0

def z572 : W := mkw 0x132b3f7f5b078747 0x826567efeb60f0e8 0xd70f3fffff0787c7 0x7ae1e7ffffe0f0f8

def z573 : W := mkw 0x006496d3a80aae1d 0x200c92da750155c3 0xe8ffffffe81ffe3f 0xfd1ffffffd03ffc7

def z574 : W := mkw 0x0ffffb3d506440e2 0x41ffff67aa0c881c 0xf7fffffff0e001c3 0xfefffffffe1c0038

def z575 : W := mkw 0x07fdfbb5e0082818 0x20ffbf76bc010503 0xefffffffe018783b 0xfdfffffffc030f07

def z576 : W := mkw 0x07dfe92456d55000 0x00fbfd248adaaa00 0xffffcd867ffff805 0xfffff9b0cfffff00

def z577 : W := mkw 0x31203fee092a87f7 0x862407fdc12550fe 0x00003ffe000007fa 0x000007ffc00000ff

def z578 : W := mkw 0x17fffb7f52078247 0x82ffff6fea40f048 0xe7ffffffe0078003 0xfcfffffffc00f000

def z579 : W := mkw 0x000204c2bedffe1d 0x2000409857dbffc3 0x180000001ffffe3c 0x0300000003ffffc7

def z580 : W := mkw 0x2966bfd9996e67fe 0x452cd7fb332dccff 0xf8eebff990e667ff 0xbf1dd7ff321cccff

def z581 : W := mkw 0x0046800010444000 0x0008d00002088800 0x70ee000010e00000 0x2e1dc000021c0000

def z582 : W := mkw 0x06dfc00016d55000 0x00dbf80002daaa00 0x77efc00017e7f801 0x2efdf80002fcff00

def z583 : W := mkw 0x0000000000000000 0x0000000000000000 0x0001c047e0000001 0x00003808fc000000

def z584 : W := mkw 0x020b000012050000 0x004160000240a000 0x400f000000078001 0x0801e0000000f000

def z585 : W := mkw 0x05902c000d900500 0x00b2058001b200a0 0xbff03c001ff807c6 0xf7fe078003ff00f8

def z586 : W := mkw 0x0a4fc07dd046624e 0x4149f80fba08cc49 0x400fc07fe0066001 0x0801f80ffc00cc00

def z587 : W := mkw 0x06dfc00016d55000 0x00dbf80002daaa00 0x7ffec00017f87800 0xafffd80002ff0f00

def z588 : W := mkw 0x05b03b0004900000 0x00b6076000920000 0xbff03f801ff80006 0xf7fe07f003ff0000

def z589 : W := mkw 0x08221259902622ee 0x4104424b3204c45d 0xd00e3279900607ff 0x3a01c64f3200c0ff

def z590 : W := mkw 0x0effd21916f550e2 0x41dffa4322deaa1c 0x77ee303817e001c0 0x2efdc60702fc0038

def z591 : W := mkw 0x026dd23540000000 0x004dba46a8000000 0xe0eff27fe0000003 0xbc1dfe4ffc000000

def z592 : W := mkw 0x1a6f927f9267e2ef 0xc34df24ff24cfc5d 0xf8efb27f90e7e7ff 0xbf1df64ff21cfcff

def z593 : W := mkw 0x0000003540000000 0x00000006a8000000 0x0000007fe0000000 0x0000000ffc000000

def z594 : W := mkw 0x08000000806060a8 0x41000000100c0c15 0x0800000000e06038 0x01000000001c0c07

def z595 : W := mkw 0x0000048228088c11 0x2000009045011182 0x0000000008199800 0x0000000001033300

def z596 : W := mkw 0x0000000004d05000 0x00000000009a0a00 0x0800000000f87800 0x01000000001f0f00

def z597 : W := mkw 0x0000040009000500 0x00000080012000a0 0x100000001f0007c4 0x0200000003e000f8

def z598 : W := mkw 0x000000c0a00a2a1c 0x2000001814014543 0x8810c3c1e01e7e3f 0x910218783c03cfc7

def z599 : W := mkw 0x000004c2a80aae1d 0x20000098550155c3 0x0011cdc7e81ff801 0x400239b8fd03ff00

def z600 : W := mkw 0x04d4c00004d05000 0x009a9800009a0a00 0xbff0c0001ff87804 0xf7fe180003ff0f00

def z601 : W := mkw 0x25b23f801ffd55b0 0x04b647f003ffaab6 0xbff03f801ffffffe 0xf7fe07f003ffffff

def z602 : W := mkw 0x0100292440000000 0x0020052488000000 0x00000d8660000000 0x000001b0cc000000

def z603 : W := mkw 0x25b03f80092805b0 0x04b607f0012500b6 0xa7f03f80000007fa 0xf4fe07f0000000ff

def z604 : W := mkw 0x000004c2a80aae1d 0x20000098550155c3 0x00114fc7e8199e3a 0x400229f8fd0333c7

def z605 : W := mkw 0x00000042a002aa0d 0x2000000854005541 0x00000047e0000000 0x00000008fc000000

def z606 : W := mkw 0x082016dba82aaeff 0x610402db750555df 0x00003fffe00007fa 0x000007fffc0000ff

def z607 : W := mkw 0x21002d8009080510 0x042005b0012100a2 0x00000d8000000000 0x000001b000000000

def z608 : W := mkw 0x0effd21916f550e2 0x41dffa4322deaa1c 0xfffff0381ffff9c5 0xfffffe0703ffff38

def z609 : W := mkw 0x01002c0009000500 0x00200580012000a0 0x00003c00000007c2 0x00000780000000f8

def z610 : W := mkw 0x04d4c080a4d87818 0x209a9810149b0f03 0x28f0c381e0f87838 0x851e18703c1f0f07

def z611 : W := mkw 0x07fdfb3540000000 0x00ffbf66a8000000 0xe7fe3fb800000002 0xfcffc7f700000000

def z612 : W := mkw 0x01203b0000000000 0x0024076000000000 0x00003f8000000002 0x000007f000000000

def z613 : W := mkw 0x0000044208028605 0x00000088410050c0 0x8011cfc7e8078607 0xd00239f8fd00f0c0

def z614 : W := mkw 0x024dc4f7e80aae1d 0x2049b89efd0155c3 0xc81fcfffe81ffe3f 0xd903f9fffd03ffc7

def z615 : W := mkw 0x29203fd9892a27fe 0x452407fb312544ff 0x00003ff9800007fa 0x000007ff300000ff

def z616 : W := mkw 0x25b03f800db805b0 0x04b607f001b700b6 0x07103f800f1807fa 0x40e207f001e300ff

def z617 : W := mkw 0x00669200106440a0 0x000cd240020c8814 0xf8eeb20010e667ff 0xbf1dd640021cccff

def z618 : W := mkw 0x00000000002000a0 0x0000000000040014 0x1800000010e007fc 0x03000000021c00ff

def z619 : W := mkw 0x0044800000000000 0x0008900000000000 0xe0ee800000000001 0xbc1dd00000000000

def z620 : W := mkw 0x130b2c6e1b078747 0x8261658dc360f0e8 0x400f3c7e000787c3 0x0801e78fc000f0f8

def z621 : W := mkw 0x000004c2a80aae1d 0x20000098550155c3 0x80010fc7e807863f 0x500021f8fd00f0c7

def z622 : W := mkw 0x0000000000000000 0x0000000000000000 0x08000000081ff804 0x010000000103ff00

def z623 : W := mkw 0x05b03f8008080410 0x00b607f001010082 0xaff03f800818063e 0xf5fe07f0010300c7

def z624 : W := mkw 0x0209002400000000 0x0041200480000000 0x400f007e00000001 0x0801e00fc0000000

def z625 : W := mkw 0x13092c6e0b038747 0x8261258dc16070e8 0x07013c7e0f0187c2 0x40e0278fc1e030f8

def z626 : W := mkw 0x17dfec261fd5d501 0x82fbfd84c3fabaa0 0xffffcc061ffff805 0xfffff980c3ffff00

def z627 : W := mkw 0x0966be59996667ee 0x412cd7cb332cccfd 0xffeebe799fe667ff 0xfffdd7cf33fcccff

def z628 : W := mkw 0x07b93b2400000000 0x00f7276480000000 0xe7ff3ffe00000003 0xfcffe7ffc0000000

def z629 : W := mkw 0x0066921110444000 0x000cd24222088800 0xf8eeb27990e66007 0xbf1dd64f321ccc00

def z630 : W := mkw 0x130b2c6e1b078747 0x8261658dc360f0e8 0x470f0c7e0f078001 0x48e1e18fc1e0f000

def z631 : W := mkw 0x2df6bb1915f441e2 0x45bed76322be883c 0x77ee303817e001c0 0x2efdc60702fc0038

def z632 : W := mkw 0x0699400006911000 0x00d3280000d22200 0xbff140001ff99804 0xf7fe280003ff3300

def z633 : W := mkw 0x0000048228088c11 0x2000009045011182 0x00000d8660000000 0x000001b0cc000000

def z634 : W := mkw 0x07fdfb75c002220c 0x00ffbf6eb8004441 0xefffffffe006663f 0xfdfffffffc00ccc7

def z635 : W := mkw 0x000004c2a80aae1d 0x20000098550155c3 0x8811c000081ffe3d 0xd10238000103ffc7

def z636 : W := mkw 0x2db03fd98dba27fe 0x45b607fb31b744ff 0xbff03ff99ff807fe 0xf7fe07ff33ff00ff

def z637 : W := mkw 0x1000006e00028247 0x8200000dc0005048 0x0000007e00000000 0x0000000fc0000000

def z638 : W := mkw 0x27ffffc2bfffffbd 0x24fffff857fffff7 0xffffffc7ffffffff 0xfffffff8ffffffff

def z639 : W := mkw 0x05b03b0000000000 0x00b6076000000000 0xa7f1ffc7e0000003 0xf4fe3ff8fc000000

def z640 : W := mkw 0x25b03f800d980510 0x04b607f001b300a2 0xa7f03f800f180002 0xf4fe07f001e30000

def z641 : W := mkw 0x0000004000020204 0x0000000800004040 0x8000004000060607 0x100000080000c0c0

def z642 : W := mkw 0x05f4fb3540000000 0x00be9f66a8000000 0x20f0ffffe0000002 0x841e1ffffc000000

def z643 : W := mkw 0x2df6bf991dfc45f2 0x45bed7f323bf88be 0xfffe3fb81ff807fe 0xffffc7f703ff00ff

def z644 : W := mkw 0x27fffb0017f551a0 0x04ffff6002feaa34 0xfffff0001ffff9c5 0xfffffe0003ffff38

def z645 : W := mkw 0x13092c260b018501 0x82612584c16030a0 0xc70f3c7e0f018003 0x78e1e78fc1e03000

def z646 : W := mkw 0x06dfc00016d55000 0x00dbf80002daaa00 0xffee800017e66005 0xbffdd00002fccc00

def z647 : W := mkw 0x00000042a002aa0d 0x2000000854005541 0x8801c247e007fe3f 0x91003848fc00ffc7

def z648 : W := mkw 0x07fdfb3540000000 0x00ffbf66a8000000 0xe7eeb27980000003 0xbcfdd64f30000000

def z649 : W := mkw 0x00201200002000a0 0x0004024000040014 0x30e0300010e001c0 0x261c0600021c0038

def z650 : W := mkw 0x07fdfb77e002aa0d 0x20ffbf6efc005541 0xe7ffffffe007f803 0xfcfffffffc00ff00

def z651 : W := mkw 0x04d4c00000000000 0x009a980000000000 0x20f0c00000000000 0x841e180000000000

def z652 : W := mkw 0x0000000080002008 0x0000000010000401 0x0800820180006038 0x8100104030000c07

def z653 : W := mkw 0x07fdfb3540000000 0x00ffbf66a8000000 0x67fef3b9e0000000 0xacffde773c000000

def z654 : W := mkw 0x0000008000080010 0x0000001000010002 0x0810038000180038 0x8102007000030007

def z655 : W := mkw 0x06dfc4801edd5410 0x00dbf89003dbaa82 0xffffcf801ffffe3f 0xfffff9f003ffffc7

def z656 : W := mkw 0x0000048228088c11 0x2000009045011182 0x8011cfc7e8199803 0xd00239f8fd033300

def z657 : W := mkw 0x04f4d31144d05000 0x009e9a62289a0a00 0x28f0c381e0f87800 0x851e18703c1f0f00

def z658 : W := mkw 0x1ffffe7f9ff7f7ef 0xc3ffffcff3fefefd 0xfffffe7f9fffffff 0xffffffcff3ffffff

def z659 : W := mkw 0x07b97b2440000000 0x00f72f6488000000 0xa7f17f8660000002 0xf4fe2ff0cc000000

def z660 : W := mkw 0x17dfec6e1b078747 0x82fbfd8dc360f0e8 0xf7fffc7e1f0787c7 0xfeffff8fc3e0f0f8

def z661 : W := mkw 0x0490000000000000 0x0092000000000000 0xa7f0000000000000 0xf4fe000000000000

def z662 : W := mkw 0x04d6c00016d55000 0x009ad80002daaa00 0x38f0c0001ffff804 0x871e180003ffff00

def z663 : W := mkw 0x1002004a12078247 0x820040094240f048 0x0000000000078000 0x000000000000f000

def z664 : W := mkw 0x082016dba82aaeff 0x610402db750555df 0x8811ffffe81fffff 0xd1023ffffd03ffff

def z665 : W := mkw 0x04b0130000000000 0x0096026000000000 0x20f0038000000000 0x841e007000000000

def z666 : W := mkw 0x000004c0880a261c 0x00000098110144c3 0x88108fc1881e663f 0xd10211f83103ccc7

def z667 : W := mkw 0x07fdfff7e80aae1d 0x20ffbffefd0155c3 0xe7ffffffe000063b 0xfcfffffffc0000c7

def z668 : W := mkw 0x0044800000404000 0x0008900000080800 0x28e0800000e06000 0x851c1000001c0c00

def z669 : W := mkw 0x06dfc04096d7720c 0x00dbf80812daee41 0xffffc2419ffffe3f 0xfffff84833ffffc7

def z670 : W := mkw 0x0000048008080410 0x0000009001010082 0x080000000818063c 0x01000000010300c7

def z671 : W := mkw 0x024dc00000000000 0x0049b80000000000 0x400fc00000000001 0x0801f80000000000

def z672 : W := mkw 0x0000000000000000 0x0000000000000000 0x8011c00000000001 0xd002380000000000

def z673 : W := mkw 0x0000000000000000 0x0000000000000000 0x8810000008180004 0xd102000001030000

def z674 : W := mkw 0x1002044a1b078747 0x820040894360f0e8 0xd00e30781f0787c7 0x3a01c60f03e0f0f8

def z675 : W := mkw 0x3fffbfff9fffe7ff 0xc7fff7fff3fffcff 0xffffbfff9fffe7ff 0xfffff7fff3fffcff

def z676 : W := mkw 0x25b23fc81dbe07f6 0x04b647f903b7c0fe 0xfffe3ff81ffe07ff 0xffffc7ff03ffc0ff

def z677 : W := mkw 0x04d6800014d44000 0x009ad000029a8800 0xfffe80001ffe6005 0xffffd00003ffcc00

def z678 : W := mkw 0x06fdd31140000000 0x00dfba6228000000 0xe7ffc381e0000001 0xfcfff8703c000000

def z679 : W := mkw 0x0a6f9259926762ee 0x414df24b324cec5d 0xffefb2799fe7e7ff 0xfffdf64f33fcfcff

def z680 : W := mkw 0x0020120000000000 0x0004024000000000 0xa0e0320000000002 0xb41c064000000000

def z681 : W := mkw 0x13092ce6ab0baf1d 0xa261259cd56175e3 0x8f11cfc7ef1ffe3f 0xd1e239f8fde3ffc7

def z682 : W := mkw 0x000004c2a80aae1d 0x20000098550155c3 0x0000000000000638 0x00000000000000c7

def z683 : W := mkw 0x08669219106440e2 0x410cd243220c881c 0xf0eeb27990e001c3 0xbe1dd64f321c0038

def z684 : W := mkw 0x0046804810464246 0x0008d0090208c848 0xf8eeb07810e667c7 0xbf1dd60f021cccf8

def z685 : W := mkw 0x11002c6e09028747 0x8220058dc12050e8 0x97003c7e1f0007c6 0x72e0078fc3e000f8

def z686 : W := mkw 0x000004c2a80aae1d 0x20000098550155c3 0x08000fc7e81ffe3e 0x010001f8fd03ffc7

def z687 : W := mkw 0x04d4c4c2acdafe1d 0x209a9898559b5fc3 0xa8f1cfc7e8fffe3f 0xd51e39f8fd1fffc7

def z688 : W := mkw 0x26ffd38016fd50b0 0x04dffa7002dfaa16 0xffffc3801ffff83d 0xfffff87003ffff07

def z689 : W := mkw 0x2fffffd99fff77fe 0x45fffffb33ffeeff 0xfffffff99fffffff 0xffffffff33ffffff

def z690 : W := mkw 0x37bb3b2c17b501e2 0x86f7676582f6a03c 0x77ee303817e001c0 0x2efdc60702fc0038

def z691 : W := mkw 0x07fffff7fedffe1d 0x20fffffeffdbffc3 0xfffffffffffffe3f 0xffffffffffffffc7

def z692 : W := mkw 0x0699400000000000 0x00d3280000000000 0x0711400000000000 0x40e2280000000000

def z693 : W := mkw 0x07fdfb3540000000 0x00ffbf66a8000000 0xe7ef3c7e00000003 0x7cfde78fc0000000

def z694 : W := mkw 0x25b03f800db805b0 0x04b607f001b700b6 0x28f03f8000f807fa 0x851e07f0001f00ff

def z695 : W := mkw 0x069b000016950000 0x00d3600002d2a000 0xffff00001fff8005 0xffffe00003fff000

def z696 : W := mkw 0x00000080a0082818 0x2000001014010503 0x00000381e0000038 0x000000703c000007

def z697 : W := mkw 0x07fdfb3540000000 0x00ffbf66a8000000 0x67ff7dbe60000000 0x6cffefb7cc000000

def z698 : W := mkw 0x024fc00012455000 0x0049f8000248aa00 0xd70fc0001f07f805 0x7ae1f80003e0ff00

def z699 : W := mkw 0x11022c4a1b078747 0x822045894360f0e8 0x97003c001f0787c6 0x72e0078003e0f0f8

def z700 : W := mkw 0x000204cab80eae5f 0x200040995701d5cb 0xd81ffffff81fffff 0xfb03ffffff03ffff

def z701 : W := mkw 0x000000408002220c 0x0000000810004441 0x080000000006663c 0x010000000000ccc7

def z702 : W := mkw 0x0002044a18068647 0x000040894300d0c8 0xd00f3c7e180787c7 0x7a01e78fc300f0f8

def z703 : W := mkw 0x21203f80092805b0 0x042407f0012500b6 0x97003f801f0007fe 0x72e007f003e000ff

def z704 : W := mkw 0x17fdff374b018501 0x82ffbfe6e96030a0 0xe7ffffffef018003 0xfcfffffffde03000

def z705 : W := mkw 0x0000000000000000 0x0000000000000000 0xc00e307800000003 0x3801c60f00000000

def z706 : W := mkw 0x06ffd31156d55000 0x00dffa622adaaa00 0xffffc381fffff805 0xfffff8703fffff00

def z707 : W := mkw 0x03092c2409000500 0x00612584812000a0 0xd70e3c381f0007c6 0x7ae1c78703e000f8

def z708 : W := mkw 0x01022ccab90eaf5f 0x202045995721d5eb 0xdf1fffffff1fffff 0xfbe3ffffffe3ffff

def z709 : W := mkw 0x130b2c2e1b058543 0x82616585c360b0a8 0xd70f3c3e1f0781c5 0x7ae1e787c3e0f038

def z710 : W := mkw 0x130b286c13070346 0x8261650d8260e068 0xd70f3c7e170607c7 0x7ae1e78fc2e0c0f8

def z711 : W := mkw 0x236fff801b6d55b0 0x046dfff0036daab6 0x400fff800007fffb 0x0801fff00000ffff

def z712 : W := mkw 0x130b2c6e1b078747 0x8261658dc360f0e8 0xd70e30781f0787c7 0x3ae1c60f03e0f0f8

def z713 : W := mkw 0x21203ff7e92aafbd 0x242407fefd2555f7 0x00003fffe00007fa 0x000007fffc0000ff

def z714 : W := mkw 0x07fdfff7e80aae1d 0x20ffbffefd0155c3 0x6fee3038081ffe3c 0x2dfdc6070103ffc7

def z715 : W := mkw 0x25b03b42a5b2abad 0x24b6076854b65575 0x37e1f047f7e7f9c1 0x26fc3e08fefcff38

def z716 : W := mkw 0x05b03b0004b000a0 0x00b6076000960014 0xbff03f801ff807fe 0xf7fe07f003ff00ff

def z717 : W := mkw 0x06dfc00016d55000 0x00dbf80002daaa00 0xffef00001ffff805 0x7ffde00003ffff00

def z718 : W := mkw 0x01223b3556d55000 0x00244766aadaaa00 0x18003ffffffff806 0x030007ffffffff00

def z719 : W := mkw 0x27fffb3557f551a0 0x04ffff66aafeaa34 0x77ee303817e001c0 0x2efdc60702fc0038

def z720 : W := mkw 0x37996da60f999511 0x86f32db4c1f332a2 0x07114d860f199800 0x40e229b0c1e33300

def z721 : W := mkw 0x224dc4b54db805b0 0x0449b896a9b700b6 0x580fc07ffff807fd 0x0b01f80fffff00ff

def z722 : W := mkw 0x130b2cac1b0d0552 0x826165958361a0aa 0xdf1e3fb81f1807fe 0xfbe3c7f703e300ff

def z723 : W := mkw 0x130b282c13050142 0x826165058260a028 0xd70f3038170001c1 0x7ae1e60702e00038

def z724 : W := mkw 0x25b03f822db88db1 0x24b607f045b711b6 0xbff1ffc7fff99fff 0xf7fe3ff8ffff33ff

def z725 : W := mkw 0x1b0b2c6e9b47e74f 0xc361658dd368fce9 0xd70f3c7e1f07e7c7 0x7ae1e78fc3e0fcf8

def z726 : W := mkw 0x01203e80092805b0 0x002407d0012500b6 0xbff03f801ff807fe 0xf7fe07f003ff00ff

def z727 : W := mkw 0x130b286e13078347 0x8261650dc260f068 0xd70f3c7e170781c3 0x7ae1e78fc2e0f038

def z728 : W := mkw 0x0cf4d311c4f070a8 0x419e9a62389e0e15 0x28f0c381e0f87838 0x851e18703c1f0f07

def z729 : W := mkw 0x04d6800014d44000 0x009ad000029a8800 0xffffc0001ffff805 0xfffff80003ffff00

def z730 : W := mkw 0x15d4ec6e0dd2d747 0x82ba9d8dc1ba5ae8 0x28f0fc7e00f87fc2 0x851e1f8fc01f0ff8

def z731 : W := mkw 0x1a4f807fb247ea4f 0xe349f00ff648fd49 0x400fc07fe007f801 0x0801f80ffc00ff00

def z732 : W := mkw 0x130b2cee3b0f8f57 0xa261659dc761f1ea 0xd70f3dfe7f0787c7 0x7ae1e7bfcfe0f0f8

def z733 : W := mkw 0x130b2c6e1b078747 0x8261658dc360f0e8 0xd70ffc7e1f07ffc7 0x7ae1ff8fc3e0fff8

def z734 : W := mkw 0x08669259906662ee 0x410cd24b320ccc5d 0xf8febff990e667ff 0xff1fd7ff321cccff

def z735 : W := mkw 0x130b2cee3b0f8f57 0xa261659dc761f1ea 0xd71fffffff1f9fc7 0xfae3ffffffe3f3f8

def z736 : W := mkw 0x0866969b386cccf3 0x610cd2d3670d999e 0x70ff7dbe78f999c0 0x6e1fefb7cf1f3338

def z737 : W := mkw 0x130b2ceebb0faf5f 0xa261659dd761f5eb 0xdf0fbfffff07e7ff 0xfbe1f7ffffe0fcff

def z738 : W := mkw 0x0309282400000000 0x0061250480000000 0xc70f3fffe0000003 0x78e1e7fffc000000

def z739 : W := mkw 0x07fdfb3544d05000 0x00ffbf66a89a0a00 0xe7ffffffe0e00003 0xfcfffffffc1c0000

def z740 : W := mkw 0x0000048008080410 0x0000009001010082 0x8811cfc7e81ffe3f 0xd10239f8fd03ffc7

def z741 : W := mkw 0x21203f80092805b0 0x042407f0012500b6 0xbfe03f801fe007fe 0xf7fc07f003fc00ff

def z742 : W := mkw 0x130b282c13050142 0x826165058260a028 0xd70e3c38170001c2 0x7ae1c78702e00038

def z743 : W := mkw 0x25b03f800db805b0 0x04b607f001b700b6 0xbff13f801fff87ff 0xf7fe27f003fff0ff

def z744 : W := mkw 0x100204cabb0faf5f 0xa20040995761f5eb 0x100000001f0787fc 0x0200000003e0f0ff

def z745 : W := mkw 0x14f6d75b5b078747 0x829edaeb6b60f0e8 0x30f0c381ff0787c4 0x861e18703fe0f0f8

def z746 : W := mkw 0x0cf4d21184f070a8 0x419e9a42309e0e15 0x28e0820180e06038 0x851c1040301c0c07

def z747 : W := mkw 0x01203a00012001a0 0x0024074000240034 0xbfe0320017e007fe 0xb7fc064002fc00ff

def z748 : W := mkw 0x130b282e13058143 0x82616505c260b028 0x570f303e170181c0 0x2ae1e607c2e03038

def z749 : W := mkw 0x130b2cee3b0f8f57 0xa261659dc761f1ea 0xd70f3c7e1f1f9fc7 0x7ae1e78fc3e3f3f8

def z750 : W := mkw 0x2cf497d18cfa66bc 0x459e92fa319f4cd7 0xa8f08fc188fe663f 0xd51e11f8311fccc7

def z751 : W := mkw 0x0a4fc07dd247724e 0x4149f80fba48ee49 0x400fc07fe007f801 0x0801f80ffc00ff00

def z752 : W := mkw 0x00201200002000a0 0x0004024000040014 0xbfe032001fe007fe 0xf7fc064003fc00ff

def z753 : W := mkw 0x130b282c13050142 0x826165058260a028 0xdf1ff0381f1ff9c5 0xfbe3fe0703e3ff38

def z754 : W := mkw 0x280204cabdfeefff 0x6500409957bfddff 0x180000001ffffffc 0x0300000003ffffff

def z755 : W := mkw 0x130b2ceebb0faf5f 0xa261659dd761f5eb 0xdf0fbe7f9f1fffff 0xfbe1f7cff3e3ffff

def z756 : W := mkw 0x2dd6add99dde675e 0x45bad5bb33bbcceb 0x471e8df98f1e6001 0x48e3d1bf31e3cc00

def z757 : W := mkw 0x08669259906662ee 0x410cd24b320ccc5d 0xf8eeb27998ffffff 0xbf1dd64f331fffff

def z758 : W := mkw 0x07fdfb3540000000 0x00ffbf66a8000000 0xe7eebfffe0000003 0xbcfdd7fffc000000

def z759 : W := mkw 0x000004c2a80aae1d 0x20000098550155c3 0x0811cf87e81ffe3c 0xc10239f0fd03ffc7

def z760 : W := mkw 0x37992da40f990510 0x86f325b481f320a2 0x07100d800f180000 0x40e201b001e30000

def z761 : W := mkw 0x034de83540000000 0x0069bd06a8000000 0xc71fffffe0000003 0xf8e3fffffc000000

def z762 : W := mkw 0x07fdfb3540000000 0x00ffbf66a8000000 0x60ffffffe0000003 0x8c1ffffffc000000

def z763 : W := mkw 0x08669259906662ee 0x410cd24b320ccc5d 0xf8eff27990e7ffff 0xbf1dfe4f321cffff

def z764 : W := mkw 0x08669259926772ee 0x410cd24b324cee5d 0xf8eeb27990e7ffff 0xbf1dd64f321cffff

def z765 : W := mkw 0x0a4fc0489247724e 0x4149f8091248ee49 0x400fc0000007f801 0x0801f8000000ff00

def z766 : W := mkw 0x2cf4d39184f870b8 0x459e9a72309f0e17 0x28f0c38180f87838 0x851e1870301f0f07

def z767 : W := mkw 0x0002004810060246 0x000040090200c048 0xd70e30781f0607c7 0x7ae1c60f03e0c0f8

def z768 : W := mkw 0x030b2c6c19060746 0x0061658d8320c0e8 0xd70f3c7e1f0607c7 0x7ae1e78fc3e0c0f8

def z769 : W := mkw 0x08669219106440e2 0x410cd243220c881c 0xf8eeb23810e667ff 0xbf1dd647021cccff

def z770 : W := mkw 0x130b286e13078347 0x8261650dc260f068 0xd70f307e170787c7 0x3ae1e60fc2e0f0f8

def z771 : W := mkw 0x0799692440000000 0x00f32d2488000000 0xc71fffffe0000003 0xf8e3fffffc000000

def z772 : W := mkw 0x25b03f800db805b0 0x04b607f001b700b6 0x37e0300017e007f8 0x26fc060002fc00ff

def z773 : W := mkw 0x11022c6e19068747 0x8220458dc320d0e8 0xd70e3c7e1f0607c7 0x7ae1c78fc3e0c0f8

def z774 : W := mkw 0x130b6c6e5b078747 0x82616d8dcb60f0e8 0xd70f7c7e7f0787c7 0x7ae1ef8fcfe0f0f8

def z775 : W := mkw 0x36bb13ee16bf82f7 0x86d7627dc2d7f05e 0x68ff03fe00ff8039 0x8d1fe07fc01ff007

def z776 : W := mkw 0x130b2cee1b0f8757 0x8261659dc361f0ea 0xdf0f3c7e1f1f87ff 0x7be1e78fc3e3f0ff

def z777 : W := mkw 0x130b2c6e9b07a74f 0x8261658dd360f4e9 0xd70fbc7f9f07e7c7 0x7ae1f78ff3e0fcf8

def z778 : W := mkw 0x130b2c6c1b070746 0x8261658d8360e0e8 0xd70e3c781f0607c7 0x7ae1c78f03e0c0f8

def z779 : W := mkw 0x24f4d7914cb804b0 0x049e9af229970096 0xa8f1cfc7e8f8063f 0xd51e39f8fd1f00c7

def z780 : W := mkw 0x000204cab80eae5f 0x200040995701d5cb 0x18000000181ffffc 0x030000000303ffff

def z781 : W := mkw 0x03293b3540000000 0x00652766a8000000 0x470e3fffe0000002 0x28e1c7fffc000000

def z782 : W := mkw 0x130b2c6e1b078747 0x8261658dc360f0e8 0x570f307e1f0787c5 0x2ae1e60fc3e0f0f8

def z783 : W := mkw 0x24b016800db805b0 0x049602d001b700b6 0xbff032001ff807fe 0xf7fe064003ff00ff

def z784 : W := mkw 0x000004c2a80aae1d 0x20000098550155c3 0x9811ffc7f81fffff 0xf3023ff8ff03ffff

def z785 : W := mkw 0x130b2c6e1b078747 0x8261658dc360f0e8 0xdf0fbc7e1f07e7c7 0xfbe1f78fc3e0fcf8

def z786 : W := mkw 0x06dfc4c2bedffe1d 0x20dbf89857dbffc3 0x77ee0fc7f7e0063a 0x2efdc1f8fefc00c7

def z787 : W := mkw 0x130b2c6e1b078747 0x8261658dc360f0e8 0xffef3c7e1fe787c7 0xfffde78fc3fcf0f8

def z788 : W := mkw 0x0866925bb066eaef 0x610cd24b760cdd5d 0xf8eeb27ff0e667ff 0xbf1dd64ffe1cccff

def z789 : W := mkw 0x130b28acb30d295a 0xa26165159661a52b 0x5f1ef3b9f71879f8 0xabe3de773ee30f3f

def z790 : W := mkw 0x180204cabb6fefff 0xe3004099576dfdff 0x180000001ffffffc 0x0300000003ffffff

def z791 : W := mkw 0x08669259906662ee 0x410cd24b320ccc5d 0x78eeb27990e067fa 0xaf1dd64f321c0cff

def z792 : W := mkw 0x00201200002000a0 0x0004024000040014 0xf8ee327810e007ff 0xbf1dc64f021c00ff

def z793 : W := mkw 0x05902c800d980510 0x00b2059001b300a2 0xbff03f801ff807fe 0xf7fe07f003ff00ff

def z794 : W := mkw 0x06dfc02456d55000 0x00dbf8048adaaa00 0xffffc0067ffff805 0xfffff800cfffff00

def z795 : W := mkw 0x024f800012454000 0x0049f0000248a800 0xffffc0001ffff805 0xfffff80003ffff00

def z796 : W := mkw 0x03293b3540000000 0x00652766a8000000 0xc71fffffe0000003 0xf8e3fffffc000000

def z797 : W := mkw 0x130b2c2c1b050542 0x826165858360a0a8 0x570e30381f0007c4 0x2ae1c60703e000f8

def z798 : W := mkw 0x06dfc00016d55000 0x00dbf80002daaa00 0xffffc047fffff805 0xfffff808ffffff00

def z799 : W := mkw 0x27996da44d980510 0x04f32db489b300a2 0x07100d800f180000 0x40e201b001e30000

def z800 : W := mkw 0x1b6dbe378b61e5a9 0xc36db7c6f16c3cb5 0x2fe18e078fe1e038 0xc5fc31c0f1fc3c07

def z801 : W := mkw 0x07fdfb3544d05000 0x00ffbf66a89a0a00 0xfffffffffff87807 0xffffffffffff0f00

def z802 : W := mkw 0x130b2c6e1b078747 0x8261658dc360f0e8 0x570e3c7e1f0787c6 0x2ae1c78fc3e0f0f8

def z803 : W := mkw 0x06dfc00016d55000 0x00dbf80002daaa00 0x7ffec0001ffff804 0xafffd80003ffff00

def z804 : W := mkw 0x130b2ceebb0faf5f 0xa261659dd761f5eb 0xd71fffffff0787ff 0xfae3ffffffe0f0ff

def z805 : W := mkw 0x069b000016950000 0x00d3600002d2a000 0xffffc0001ffff805 0xfffff80003ffff00

def z806 : W := mkw 0x25b03f800db805b0 0x04b607f001b700b6 0xbff1ff801ff807ff 0xf7fe3ff003ff00ff

def z807 : W := mkw 0x130b2cee1b0f8757 0x8261659dc361f0ea 0xd71f3dfe1f1f87c7 0x7ae3e7bfc3e3f0f8

def z808 : W := mkw 0x08669219906460ea 0x410cd243320c8c1d 0xf8eeb23990e067fe 0xbf1dd647321c0cff

def z809 : W := mkw 0x03092ca409080510 0x00612594812100a2 0xdf1fffffff1807ff 0xfbe3ffffffe300ff

def z810 : W := mkw 0x0eb9525986b332ee 0x41d72a4b30d6665d 0x071172798f199ffa 0x40e22e4f31e333ff

def z811 : W := mkw 0x0a4f80599247624e 0x4149f00b3248ec49 0x400f80798007e001 0x0801f00f3000fc00

def z812 : W := mkw 0x130b282c13050142 0x826165058260a028 0x570f3c3e170001c0 0x6ae1e787c2e00038

def z813 : W := mkw 0x07fdfb3540000000 0x00ffbf66a8000000 0xefffffffe0187803 0xfdfffffffc030f00

def z814 : W := mkw 0x27fdfb35412001a0 0x04ffbf66a8240034 0xe7ffffffe00001c3 0xfcfffffffc000038

def z815 : W := mkw 0x08669259906662ee 0x410cd24b320ccc5d 0xf8eeb03810e667fd 0xbf1dd607021cccff

def z816 : W := mkw 0x130b2ceebb0faf5f 0xa261659dd761f5eb 0xdf1f7dfe7f1fffff 0x7be3efbfcfe3ffff

def z817 : W := mkw 0x130b2cee9b0fa75f 0x8261659dd361f4eb 0xdf1fbfff9f1fe7ff 0xfbe3f7fff3e3fcff

def z818 : W := mkw 0x100204caba0fae5f 0xa20040995741f5cb 0x08000000081ffe3c 0x010000000103ffc7

def z819 : W := mkw 0x16dfc02c16d55042 0x82dbf80582daaa08 0xffffc0381ffff805 0xfffff80703ffff00

def z820 : W := mkw 0x130b2c2e1b058543 0x82616585c360b0a8 0x570e30381f0181c0 0x2ae1c60703e03038

def z821 : W := mkw 0x25b03b0005b001a0 0x04b6076000b60034 0x3fe0300017e007fc 0x27fc060002fc00ff

def z822 : W := mkw 0x25b03f800db805b0 0x04b607f001b700b6 0xbff03f801ffffffe 0xf7fe07f003ffffff

def z823 : W := mkw 0x25b03b0005b001a0 0x04b6076000b60034 0x37e0320017e007fa 0x26fc064002fc00ff

def z824 : W := mkw 0x130b286c13070346 0x8261650d8260e068 0x570e3078170601c1 0x2ae1c60f02e0c038

def z825 : W := mkw 0x25b03f800db805b0 0x04b607f001b700b6 0xbfe03f8017e007fe 0xb7fc07f002fc00ff

def z826 : W := mkw 0x07b93b2400000000 0x00f7276480000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z827 : W := mkw 0x07fdfb3544900000 0x00ffbf66a8920000 0xfffffffffffff807 0xffffffffffffff00

def z828 : W := mkw 0x06fdd21100000000 0x00dfba4220000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z829 : W := mkw 0x25b03f800db805b0 0x04b607f001b700b6 0xbff03fc7fff807fe 0xf7fe07f8ffff00ff

def z830 : W := mkw 0x130b2c2e1b058543 0x82616585c360b0a8 0x570e3c3e170001c0 0x2ae1c787c2e00038

def z831 : W := mkw 0x07fdfb3540000000 0x00ffbf66a8000000 0xe7ef3fffe0000003 0x7cfde7fffc000000

def z832 : W := mkw 0x130b2c6e1b078747 0x8261658dc360f0e8 0xdf0f3e7e1f0787ff 0xfbe1e7cfc3e0f0ff

def z833 : W := mkw 0x07fdfb3541000100 0x00ffbf66a8200020 0xf7fffffff70001c3 0xfefffffffee00038

def z834 : W := mkw 0x0a4fc0599247724e 0x4149f80b3248ee49 0x400e807980066001 0x0801d00f3000cc00

def z835 : W := mkw 0x27fdfb3545900100 0x04ffbf66a8b20020 0xe7ffffffe7000003 0xfcfffffffce00000

def z836 : W := mkw 0x130b2c6e1b078747 0x8261658dc360f0e8 0x570e3038170007c0 0x2ae1c60702e000f8

def z837 : W := mkw 0x036dfb3540000000 0x006dbf66a8000000 0xc70fffffe0000003 0x78e1fffffc000000

def z838 : W := mkw 0x37996da64f998511 0x86f32db4c9f330a2 0x07114d866f198000 0x40e229b0cde33000

def z839 : W := mkw 0x08669259906662ee 0x410cd24b320ccc5d 0xf8ee307810e667ff 0x3f1dc60f021cccff

def z840 : W := mkw 0x130b2ceebb0faf5f 0xa261659dd761f5eb 0x5f0e30381f1ffffc 0x2be1c60703e3ffff

def z841 : W := mkw 0x24f4d7d3ecbaaebd 0x249e9afa7d9755d7 0xa8f1cfc7e8fffe3f 0xd51e39f8fd1fffc7

def z842 : W := mkw 0x08669259906662ee 0x410cd24b320ccc5d 0xf8fff27990e667ff 0xff1ffe4f321cccff

def z843 : W := mkw 0x25b03f800db805b0 0x04b607f001b700b6 0xb7e03f801fe007fe 0x76fc07f003fc00ff

def z844 : W := mkw 0x300204cabfbfafff 0xa600409957f7f5ff 0x180000001ffffffc 0x0300000003ffffff

def z845 : W := mkw 0x08669259906662ee 0x410cd24b320ccc5d 0xffeeb2799fe667ff 0xfffdd64f33fcccff

def z846 : W := mkw 0x31203feea92aafff 0xa62407fdd52555ff 0x00003fffe00007fa 0x000007fffc0000ff

def z847 : W := mkw 0x25b03f800db805b0 0x04b607f001b700b6 0x3ff00f801ff807fc 0xc7fe01f003ff00ff

def z848 : W := mkw 0x01203b3540000000 0x00240766a8000000 0xc00e3fffe0000003 0x3801c7fffc000000

def z849 : W := mkw 0x17996ca62f999d11 0xa2f32d94c5f333a2 0x07114d866f199800 0x40e229b0cde33300

def z850 : W := mkw 0x08669259906662ee 0x410cd24b320ccc5d 0xf8eebffff0e667ff 0xbf1dd7fffe1cccff

def z851 : W := mkw 0x06dfc00016d55000 0x00dbf80002daaa00 0xffee80001ffff805 0xbffdd00003ffff00

def z852 : W := mkw 0x19203effa92aafff 0xe32407dff52555ff 0x00003fffe00007fa 0x000007fffc0000ff

def z853 : W := mkw 0x0ffdfb35406040a0 0x41ffbf66a80c0814 0xe7ffffffe0e00003 0xfcfffffffc1c0000

def z854 : W := mkw 0x130b2ceebb0faf5f 0xa261659dd761f5eb 0xdf0ffc7fff1fffff 0x7be1ff8fffe3ffff

def z855 : W := mkw 0x130b2c6e1b078747 0x8261658dc360f0e8 0xd70e3c7e1f0007c6 0x7ae1c78fc3e000f8

def z856 : W := mkw 0x024dc03540000000 0x0049b806a8000000 0x401fcdffe0000001 0x4803f9bffc000000

def z857 : W := mkw 0x000004c2a80aae1d 0x20000098550155c3 0x0011cfc7e81ffe3b 0x400239f8fd03ffc7

def z858 : W := mkw 0x0309282401000100 0x0061250480200020 0x570e3038170001c0 0x2ae1c60702e00038

def z859 : W := mkw 0x100204cabfdfff5f 0xa200409957fbffeb 0x180000001ffffffc 0x0300000003ffffff

def z860 : W := mkw 0x130b2ceebb0faf5f 0xa261659dd761f5eb 0xdf0f3fffff1fffff 0x7be1e7ffffe3ffff

def z861 : W := mkw 0x00649211002000a0 0x000c924220040014 0xf8ee323810e007fe 0xbf1dc647021c00ff

def z862 : W := mkw 0x25b03b8005b801b0 0x04b6077000b70036 0xbff0338017f807fe 0xb7fe067002ff00ff

def z863 : W := mkw 0x07fdfb3546911000 0x00ffbf66a8d22200 0xefffffffef1ff807 0xfdfffffffde3ff00

def z864 : W := mkw 0x37992da62f998d11 0xa6f325b4c5f331a2 0x07114d866f199800 0x40e229b0cde33300

def z865 : W := mkw 0x130b2c6e1b078747 0x8261658dc360f0e8 0xd71ffc7e1f0787c7 0xfae3ff8fc3e0f0f8

def z866 : W := mkw 0x08669259906662ee 0x410cd24b320ccc5d 0x78eeb07990e667fd 0x2f1dd60f321cccff

def z867 : W := mkw 0x130b2c6e1b078747 0x8261658dc360f0e8 0xd70e3c7e170607c7 0x3ae1c78fc2e0c0f8

def z868 : W := mkw 0x06dfc00816d55042 0x00dbf80102daaa08 0xfffff0381ffff9c5 0xfffffe0703ffff38

def z869 : W := mkw 0x27992da40d980510 0x04f325b481b300a2 0x07110d860f180000 0x40e221b0c1e30000

def z870 : W := mkw 0x00669259102602e6 0x000cd24b2204c05c 0xf8eeb27990e607ff 0xbf1dd64f321cc0ff

def z871 : W := mkw 0x27fdfb3544b000a0 0x04ffbf66a8960014 0xe7ffffffe0e00003 0xfcfffffffc1c0000

def z872 : W := mkw 0x130b2c6e1b078747 0x8261658dc360f0e8 0xd71f3ffe1f0787c7 0xfae3e7ffc3e0f0f8

def z873 : W := mkw 0x08669259106642e6 0x410cd24b220cc85c 0xf8ee327810e607ff 0xbf1dc64f021cc0ff

def z874 : W := mkw 0x25902c800db805b0 0x04b2059001b700b6 0xbff03c001ff807fe 0xf7fe078003ff00ff

def z875 : W := mkw 0x06ddc00004900000 0x00dbb80000920000 0xffffc0001ffff805 0xfffff80003ffff00

def z876 : W := mkw 0x21203fc2a92aafbd 0x242407f8552555f7 0x00003f80000007fa 0x000007f0000000ff

def z877 : W := mkw 0x24f4d31144b000a0 0x049e9a6228960014 0x20f0c381e0e00000 0x841e18703c1c0000

def z878 : W := mkw 0x06dfc00016d55000 0x00dbf80002daaa00 0xfffff0001fffffc7 0xfffffe0003fffff8

def z879 : W := mkw 0x25b03b0005b001a0 0x04b6076000b60034 0xbff03f8017e007fe 0xf7fe07f002fc00ff

def z880 : W := mkw 0x130b2c6e1b078747 0x8261658dc360f0e8 0x570f3c7e1f0781c1 0x6ae1e78fc3e0f038

def z881 : W := mkw 0x00221208102400e2 0x000442410204801c 0xf8ee323810e007fe 0xbf1dc647021c00ff

def z882 : W := mkw 0x25b03fa44db805b0 0x04b607f489b700b6 0xbff03f867ff807fe 0xf7fe07f0cfff00ff

def z883 : W := mkw 0x0cf4d21104f050a0 0x419e9a42209e0a14 0x20e0000000e00000 0x041c0000001c0000

def z884 : W := mkw 0x004680489046624e 0x0008d0091208cc49 0xf8eeb27990e667ff 0xbf1dd64f321cccff

def z885 : W := mkw 0x0000000000000000 0x0000000000000000 0xc01fffffe0000003 0xf803fffffc000000

def z886 : W := mkw 0x0209002400000000 0x0041200480000000 0xc01fcfffe0000003 0xd803f9fffc000000

def z887 : W := mkw 0x130b2c6e1b078747 0x8261658dc360f0e8 0xdf1fffffff1fffc7 0xfbe3ffffffe3fff8

def z888 : W := mkw 0x0cf4d25184f272ac 0x419e9a4a309e4e55 0xa8f1c24188fffe3f 0xd51e3848311fffc7

def z889 : W := mkw 0x0f9b696cd06662ee 0x41f36d2d9a0ccc5d 0x1f114d8670e667fc 0x43e229b0ce1cccff

def z890 : W := mkw 0x130b2c2c1b050542 0x826165858360a0a8 0xd70f3c7e1f0007c7 0x7ae1e78fc3e000f8

def z891 : W := mkw 0x130b2c6e3b078f47 0xa261658dc760f1e8 0xd70f7c7e7f079fc7 0x7ae1ef8fcfe0f3f8

def z892 : W := mkw 0x069b400016d55000 0x00d3680002daaa00 0xbff140001ffff804 0xf7fe280003ffff00

def z893 : W := mkw 0x2cf4d391c4f860b8 0x459e9a72389f0c17 0x28f0c381e0f86038 0x851e18703c1f0c07

def z894 : W := mkw 0x04d6c00016d55000 0x009ad80002daaa00 0xbff0c0001ffff804 0xf7fe180003ffff00

def z895 : W := mkw 0x130b2c2c1b050542 0x826165858360a0a8 0x570e3c381f0001c0 0x6ae1c78703e00038

def z896 : W := mkw 0x25b03f800db805b0 0x04b607f001b700b6 0xbff0ff801ff87ffe 0xf7fe1ff003ff0fff

def z897 : W := mkw 0x130b286e13078347 0x8261650dc260f068 0x570e307e170001c0 0x2ae1c60fc2e00038

def z898 : W := mkw 0x05b03f00092005a0 0x00b607e0012400b4 0xbff03f801fe007fe 0xf7fe07f003fc00ff

def z899 : W := mkw 0x03092ce6a90aaf1d 0x2061259cd52155e3 0xdf1fffffff1fffff 0xfbe3ffffffe3ffff

def z900 : W := mkw 0x020b004812070246 0x004160090240e048 0xd70e3078170607c7 0x3ae1c60f02e0c0f8

def z901 : W := mkw 0x00669248106642e6 0x000cd249020cc85c 0xf8eeb27810e667ff 0xbf1dd64f021cccff

def z902 : W := mkw 0x130b2c6ebb07af4f 0xa261658dd760f5e9 0xdf0ffe7fff07ffff 0xfbe1ffcfffe0ffff

def z903 : W := mkw 0x24f4d391e4b828b8 0x249e9a723c970517 0x28f0c381e0f87838 0x851e18703c1f0f07

def z904 : W := mkw 0x07dde82400000000 0x00fbbd0480000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z905 : W := mkw 0x130b2c2c1b050542 0x826165858360a0a8 0x570e3c38170007c2 0x2ae1c78702e000f8

def z906 : W := mkw 0x036dfb3540000000 0x006dbf66a8000000 0xc01fffffe0000003 0xd803fffffc000000

def z907 : W := mkw 0x130b2c6e1b078747 0x8261658dc360f0e8 0xdf0f3c7e1f1fffc7 0x7be1e78fc3e3fff8

def z908 : W := mkw 0x06dfc10056d55000 0x00dbf8200adaaa00 0xffffc1807ffff805 0xfffff8300fffff00

def z909 : W := mkw 0x0102284811060346 0x002045090220c068 0xd70e3078170607c7 0x3ae1c60f02e0c0f8

def z910 : W := mkw 0x2cf49391a4f868b8 0x659e9272349f0d17 0x28f0c381e0f87838 0x851e18703c1f0f07

def z911 : W := mkw 0x130b2cee1b0f8757 0x8261659dc361f0ea 0xdf1ffffe1f1fffff 0xfbe3ffffc3e3ffff

def z912 : W := mkw 0x04f4d31140000000 0x009e9a6228000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z913 : W := mkw 0x0edfc01916d55042 0x41dbf80322daaa08 0xffffc0381ffff805 0xfffff80703ffff00

def z914 : W := mkw 0x130b2ceebb0faf5f 0xa261659dd761f5eb 0xd71f7fffff1f9fff 0x7ae3efffffe3f3ff

def z915 : W := mkw 0x13092c6e09028747 0x8261258dc12050e8 0xd70f3c7e1f0007c7 0x7ae1e78fc3e000f8

def z916 : W := mkw 0x06dfc01156d55000 0x00dbf8022adaaa00 0xffffc001fffff805 0xfffff8003fffff00

def z917 : W := mkw 0x08669259906662ee 0x410cd24b320ccc5d 0xf0ee327990e607ff 0x3e1dc64f321cc0ff

def z918 : W := mkw 0x07fdfb3540000000 0x00ffbf66a8000000 0x67efffffe0000003 0x2cfdfffffc000000

def z919 : W := mkw 0x020b00489207224e 0x004160091240e449 0xdf1ff2799f1fffff 0xfbe3fe4f33e3ffff

def z920 : W := mkw 0x0ffffb3d56f550e2 0x41ffff67aadeaa1c 0x77ee303817e001c0 0x2efdc60702fc0038

def z921 : W := mkw 0x0866925bb066eaef 0x610cd24b760cdd5d 0xf8fff27ff8ffffff 0xff1ffe4fff1fffff

def z922 : W := mkw 0x1a4f807d9247624e 0xc349f00fb248ec49 0x400e807980066001 0x0801d00f3000cc00

def z923 : W := mkw 0x07fdfb3540000000 0x00ffbf66a8000000 0xefffffffe0066007 0xfdfffffffc00cc00

def z924 : W := mkw 0x0064921100000000 0x000c924220000000 0xe0eebfffe0000003 0xbc1dd7fffc000000

def z925 : W := mkw 0x17fdfb3543010100 0x82ffbf66a8602020 0xe7ffffffe7000003 0xfcfffffffce00000

def z926 : W := mkw 0x00649251802222ac 0x000c924a30044455 0xf8eeb27990e667ff 0xbf1dd64f321cccff

def z927 : W := mkw 0x130b2c6e1b47d747 0x8261658dc368fae8 0xd70f3c7e1f07ffc7 0x7ae1e78fc3e0fff8

def z928 : W := mkw 0x130b2c6ebb07af4f 0xa261658dd760f5e9 0xd70f3c7fff0787c7 0x7ae1e78fffe0f0f8

def z929 : W := mkw 0x130b282c13050142 0x826165058260a028 0xd71ffffff70001c3 0xfae3fffffee00038

def z930 : W := mkw 0x000004c2a90aaf1d 0x20000098552155e3 0x9811cfc7ff1fffff 0xd30239f8ffe3ffff

def z931 : W := mkw 0x07fdfb3540404000 0x00ffbf66a8080800 0xefffffffe0e06003 0xfdfffffffc1c0c00

def z932 : W := mkw 0x07fdfb3544900000 0x00ffbf66a8920000 0xf7fffffff7e00003 0xfefffffffefc0000

def z933 : W := mkw 0x07b93b3540000000 0x00f72766a8000000 0xe7ff3fffe0000003 0xfcffe7fffc000000

def z934 : W := mkw 0x036dbb3540000000 0x006db766a8000000 0xe7efbfffe0000003 0xfcfdf7fffc000000

def z935 : W := mkw 0x08649211806060a8 0x410c9242300c0c15 0xf8eeb27990e067ff 0xbf1dd64f321c0cff

def z936 : W := mkw 0x03293b3540000000 0x00652766a8000000 0x400f3fffe0000003 0x0801e7fffc000000

def z937 : W := mkw 0x00221248902622ee 0x000442491204c45d 0xf8eeb27990e667ff 0xbf1dd64f321cccff

def z938 : W := mkw 0x130b2c6e1b078747 0x8261658dc360f0e8 0xd71f7dfe7f0787c7 0x7ae3efbfcfe0f0f8

def z939 : W := mkw 0x35b03fa60db885b1 0x86b607f4c1b710b6 0xbff03f861ff807fe 0xf7fe07f0c3ff00ff

def z940 : W := mkw 0x07fdfb3540000000 0x00ffbf66a8000000 0xf7ffffffff000007 0xfeffffffffe00000

def z941 : W := mkw 0x036dfb3540000000 0x006dbf66a8000000 0x400e3fffe0000002 0x0801c7fffc000000

def z942 : W := mkw 0x130b282c13050142 0x826165058260a028 0x570e3c7e170001c2 0x2ae1c78fc2e00038

def z943 : W := mkw 0x07dde93540000000 0x00fbbd26a8000000 0xe7ffcdffe0000001 0xfcfff9bffc000000

def z944 : W := mkw 0x25b03fa40db805b0 0x04b607f481b700b6 0xbff03ffe1ff807fe 0xf7fe07ffc3ff00ff

def z945 : W := mkw 0x130b2c6e9b07a74f 0x8261658dd360f4e9 0xdf1fffffff07e7ff 0xfbe3ffffffe0fcff

def z946 : W := mkw 0x030b286c12070246 0x0061650d8240e048 0xd70f3c7e1f0787c7 0x7ae1e78fc3e0f0f8

def z947 : W := mkw 0x130b286c13070346 0x8261650d8260e068 0x570e3078170007c2 0x2ae1c60f02e000f8

def z948 : W := mkw 0x08221259902622ee 0x4104424b3204c45d 0xf8ee327990e607ff 0xbf1dc64f321cc0ff

def z949 : W := mkw 0x130b2ceebb0faf5f 0xa261659dd761f5eb 0xd70f3c7e1f0787ff 0x7ae1e78fc3e0f0ff

def z950 : W := mkw 0x27fdfb3545b001a0 0x04ffbf66a8b60034 0xfffffffff7e007ff 0xfffffffffefc00ff

def z951 : W := mkw 0x07fdfb3544900000 0x00ffbf66a8920000 0xe7ffffffef180003 0xfcfffffffde30000

def z952 : W := mkw 0x000004c2a80aae1d 0x20000098550155c3 0x0811cfc7e01ffe3b 0x810239f8fc03ffc7

def z953 : W := mkw 0x06ddc03540000000 0x00dbb806a8000000 0xe7ffcfffe0000003 0xfcfff9fffc000000

def z954 : W := mkw 0x07fdfb3546911000 0x00ffbf66a8d22200 0xe7ffffffe7000003 0xfcfffffffce00000

def z955 : W := mkw 0x25b03f800db805b0 0x04b607f001b700b6 0x37f03f801ff807fa 0x66fe07f003ff00ff

def z956 : W := mkw 0x06dfc00016d55000 0x00dbf80002daaa00 0x7fefc0001ffff805 0x2ffdf80003ffff00

def z957 : W := mkw 0x130b2c6e1b078747 0x8261658dc360f0e8 0xd71f7c7e1f1f9fc7 0x7ae3ef8fc3e3f3f8

def z958 : W := mkw 0x08669259906662ee 0x410cd24b320ccc5d 0xf8feb27998fe67ff 0xff1fd64f331fccff

def z959 : W := mkw 0x01002c0009000500 0x00200580012000a0 0xd70e3c781f0007c7 0x7ae1c78f03e000f8

def z960 : W := mkw 0x08669259b0666aee 0x610cd24b360ccd5d 0xf8eef279f0e67fff 0xbf1dde4f3e1ccfff

def z961 : W := mkw 0x07fdfb3540000000 0x00ffbf66a8000000 0x67ffcfffe0000001 0xccfff9fffc000000

def z962 : W := mkw 0x080204cab84eee5f 0x610040995709ddcb 0x08000000081ffe3c 0x010000000103ffc7

def z963 : W := mkw 0x130b2c6e9b07a74f 0x8261658dd360f4e9 0xdf0f3c7e1f07e7ff 0x7be1e78fc3e0fcff

def z964 : W := mkw 0x130b2ceebb0faf5f 0xa261659dd761f5eb 0xdf1f3fffff1f87ff 0xfbe3e7ffffe3f0ff

def z965 : W := mkw 0x06dfc00016d55000 0x00dbf80002daaa00 0xffffc2419ffff807 0xfffff84833ffff00

def z966 : W := mkw 0x0490000004900000 0x0092000000920000 0xbff000001ffff804 0xf7fe000003ffff00

def z967 : W := mkw 0x130b2c6e9b07a74f 0x8261658dd360f4e9 0xdf1ffe7f9f1fffff 0xfbe3ffcff3e3ffff

def z968 : W := mkw 0x25b07f800db815b0 0x04b60ff001b702b6 0xbff07f801ff81ffe 0xf7fe0ff003ff03ff

def z969 : W := mkw 0x25b03f800db805b0 0x04b607f001b700b6 0xbff030001ff807fc 0xf7fe060003ff00ff

def z970 : W := mkw 0x0866925b9066e2ef 0x410cd24b720cdc5d 0xf8efb27f90e7e7ff 0xbf1df64ff21cfcff

def z971 : W := mkw 0x07fdfb3544d05000 0x00ffbf66a89a0a00 0xefffffffe8fff807 0xfdfffffffd1fff00

def z972 : W := mkw 0x06dfc02416d55000 0x00dbf80482daaa00 0xffffc07e1ffff805 0xfffff80fc3ffff00

def z973 : W := mkw 0x07fdfb35402000a0 0x00ffbf66a8040014 0xefffffffe0e0003b 0xfdfffffffc1c0007

def z974 : W := mkw 0x25b03f800db805b0 0x04b607f001b700b6 0xbfe032001ff807fe 0xb7fc064003ff00ff

def z975 : W := mkw 0x06dfc00016d55000 0x00dbf80002daaa00 0x6fffc0000ffff801 0xcdfff80001ffff00

def z976 : W := mkw 0x2cf497d3acfaeebd 0x659e92fa759f5dd7 0xa8f1cfc7e8fffe3f 0xd51e39f8fd1fffc7

def z977 : W := mkw 0x130b2c6e1b078747 0x8261658dc360f0e8 0xd70e3c381f0787c6 0x7ae1c78703e0f0f8

def z978 : W := mkw 0x026dd23540000000 0x004dba46a8000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z979 : W := mkw 0x01022cc8990e275e 0x002045991321c4eb 0xdf1ebff99f1e67ff 0xfbe3d7ff33e3ccff

def z980 : W := mkw 0x100004caa90aaf5f 0xa2000099552155eb 0x8811cfc7e81fffff 0xd10239f8fd03ffff

def z981 : W := mkw 0x080204cab86eeeff 0x61004099570ddddf 0x1800000010e667fc 0x03000000021cccff

def z982 : W := mkw 0x07fdfb3540000000 0x00ffbf66a8000000 0x67fffdffe0000001 0x6cffffbffc000000

def z983 : W := mkw 0x06dfc03556d55000 0x00dbf806aadaaa00 0xffffcffffffff807 0xfffff9ffffffff00

def z984 : W := mkw 0x05f4bb1100000000 0x00be976220000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z985 : W := mkw 0x25b03f000db005a0 0x04b607e001b600b4 0xbfe03e001fe007fe 0xf7fc07c003fc00ff

def z986 : W := mkw 0x25b03f800db805b0 0x04b607f001b700b6 0xbff1ffc7ffffffff 0xf7fe3ff8ffffffff

def z987 : W := mkw 0x130b282c13050142 0x826165058260a028 0xd70e3078170001c3 0x3ae1c60f02e00038

def z988 : W := mkw 0x07fdfb3546d15000 0x00ffbf66a8da2a00 0xefffffffeff9f803 0xfdfffffffdff3f00

def z989 : W := mkw 0x249004800db805b0 0x0492009001b700b6 0x3fe000001ff807fc 0x27fc000003ff00ff

def z990 : W := mkw 0x25b03f914db805b0 0x04b607f229b700b6 0xbff03f81fff807fe 0xf7fe07f03fff00ff

def z991 : W := mkw 0x0866d259d06662ee 0x410cda4b3a0ccc5d 0xf8eef279f0e667ff 0xbf1dde4f3e1cccff

def z992 : W := mkw 0x07fdfb3540000000 0x00ffbf66a8000000 0x67feffffe0000002 0xacffdffffc000000

def z993 : W := mkw 0x0866925bb066eaef 0x610cd24b760cdd5d 0xf8eeb27990e7ffff 0xbf1dd64f321cffff

def z994 : W := mkw 0x130b2d6e5b078747 0x826165adcb60f0e8 0xd70f3dfe7f0787c7 0x7ae1e7bfcfe0f0f8

def z995 : W := mkw 0x130b2c6e1b078747 0x8261658dc360f0e8 0x570f3c7e1f0187c2 0x6ae1e78fc3e030f8

def z996 : W := mkw 0x020b044a1a078647 0x004160894340f0c8 0xd70f3c7e1f0787c7 0x7ae1e78fc3e0f0f8

def z997 : W := mkw 0x07fdfb3542010000 0x00ffbf66a8402000 0xe7ffffffef018003 0xfcfffffffde03000

def z998 : W := mkw 0x130b286c13070346 0x8261650d8260e068 0x570e3038170607c4 0x2ae1c60702e0c0f8

def z999 : W := mkw 0x130b2ceebb0faf5f 0xa261659dd761f5eb 0x570e3ffff70007fa 0x2ae1c7fffee000ff

def z1000 : W := mkw 0x25b03f800db805b0 0x04b607f001b700b6 0x3ff033801ff807fc 0xa7fe067003ff00ff

def z1001 : W := mkw 0x06dfc00016d55000 0x00dbf80002daaa00 0xffffc381fffff805 0xfffff8703fffff00

def z1002 : W := mkw 0x11022c4a1b078747 0x822045894360f0e8 0xd70e3c781f0787c7 0x7ae1c78f03e0f0f8

def z1003 : W := mkw 0x08669219106440e2 0x410cd243220c881c 0xf8eeb27990e007ff 0xbf1dd64f321c00ff

def z1004 : W := mkw 0x08649259802222ee 0x410c924b3004445d 0xf8eeb27990e007ff 0xbf1dd64f321c00ff

def z1005 : W := mkw 0x130b2c6e1b078747 0x8261658dc360f0e8 0x470f3c7e0f0787c3 0x48e1e78fc1e0f0f8

def z1006 : W := mkw 0x130b2ceebb0faf5f 0xa261659dd761f5eb 0xd71ffdffff1fffc7 0x7ae3ffbfffe3fff8

def z1007 : W := mkw 0x04b016800cb804b0 0x009602d001970096 0xbff03f801ff807fe 0xf7fe07f003ff00ff

def z1008 : W := mkw 0x1a4fc07f9247f24f 0xc349f80ff248fe49 0x400fc07f8007f801 0x0801f80ff000ff00

def z1009 : W := mkw 0x130b6c6e1b079747 0x82616d8dc360f2e8 0xd70f7c7e1f079fc7 0x7ae1ef8fc3e0f3f8

def z1010 : W := mkw 0x130b2c6e1b078747 0x8261658dc360f0e8 0x570f3c7e170787c3 0x2ae1e78fc2e0f0f8

def z1011 : W := mkw 0x0492000016d55000 0x0092400002daaa00 0xbff1c0001ffff805 0xf7fe380003ffff00

def z1012 : W := mkw 0x08669259906662ee 0x410cd24b320ccc5d 0xf0eeb27990e007fb 0xbe1dd64f321c00ff

def z1013 : W := mkw 0x25b03f800db805b0 0x04b607f001b700b6 0xbff0bfc19ff807ff 0xf7fe17f833ff00ff

def z1014 : W := mkw 0x06dfc00016d55000 0x00dbf80002daaa00 0xffffcc461ffff807 0xfffff988c3ffff00

def z1015 : W := mkw 0x01022c4a19068747 0x002045894320d0e8 0xd70f3c7e1f0787c7 0x7ae1e78fc3e0f0f8

def z1016 : W := mkw 0x130b2c6e1b078747 0x8261658dc360f0e8 0xdf1f3c7e1f1f87c7 0xfbe3e78fc3e3f0f8

def z1017 : W := mkw 0x130b2cee3b0f8f57 0xa261659dc761f1ea 0xdf1ffdfe7f1fffc7 0xfbe3ffbfcfe3fff8

def z1018 : W := mkw 0x25b03b0005b001a0 0x04b6076000b60034 0xbff032001ff807fe 0xf7fe064003ff00ff

def z1019 : W := mkw 0x0164bb3540000000 0x002c9766a8000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z1020 : W := mkw 0x00000080a0082818 0x2000001014010503 0x8811cfc7e81ff83f 0xd10239f8fd03ff07

def z1021 : W := mkw 0x07fdfb35402000a0 0x00ffbf66a8040014 0xe7ffffffe00007fb 0xfcfffffffc0000ff

def z1022 : W := mkw 0x130b2c6e1b078747 0x8261658dc360f0e8 0xd70fbe7f9f0787c7 0xfae1f7cff3e0f0f8

def z1023 : W := mkw 0x24b017800db805b0 0x049602f001b700b6 0xbff003801ff807fc 0xf7fe007003ff00ff

def z1024 : W := mkw 0x07fdfb3544b000a0 0x00ffbf66a8960014 0xfffffffffff807ff 0xffffffffffff00ff

def z1025 : W := mkw 0x08669219106440e2 0x410cd243220c881c 0x70ee323810e007fa 0x2e1dc647021c00ff

def z1026 : W := mkw 0x124fc06eb247fa4f 0xa249f80dd648ff49 0x400fc07fe007f801 0x0801f80ffc00ff00

def z1027 : W := mkw 0x030b2c481b070746 0x006165890360e0e8 0xd70f3c781f0787c7 0x7ae1e78f03e0f0f8

def z1028 : W := mkw 0x24f4939104b800b0 0x049e927220970016 0x28f0838180f80038 0x851e1070301f0007

def z1029 : W := mkw 0x000004c2a80aae1d 0x20000098550155c3 0x0811cfc7e81ff839 0xc10239f8fd03ff07

def z1030 : W := mkw 0x27996da66d988d11 0x24f32db4cdb311a2 0x07114d866f199800 0x40e229b0cde33300

def z1031 : W := mkw 0x13092c260b018501 0x82612584c16030a0 0xd70f3c7e1f0187c7 0x7ae1e78fc3e030f8

def z1032 : W := mkw 0x29203fdba92aafff 0x652407fb752555ff 0x00003fffe00007fa 0x000007fffc0000ff

def z1033 : W := mkw 0x130b282c13050142 0x826165058260a028 0xd70e30381f0001c4 0x7ae1c60703e00038

def z1034 : W := mkw 0x25b03f800db805b0 0x04b607f001b700b6 0xbff0ff81fff807fe 0xf7fe1ff03fff00ff

def z1035 : W := mkw 0x08468048906662ee 0x4108d009120ccc5d 0xf8eeb07810e667ff 0xbf1dd60f021cccff

def z1036 : W := mkw 0x330b2dee1b0f8757 0x866165bdc361f0ea 0xd70f3dfe1f0787c7 0x7ae1e7bfc3e0f0f8

def z1037 : W := mkw 0x21203e800db805b0 0x042407d001b700b6 0xbfe03e001ff807fe 0xf7fc07c003ff00ff

def z1038 : W := mkw 0x08221248906662ee 0x41044249120ccc5d 0xf8ee327810e667ff 0xbf1dc64f021cccff

def z1039 : W := mkw 0x08669259906662ee 0x410cd24b320ccc5d 0xf8ee327990e007fe 0xbf1dc64f321c00ff

def z1040 : W := mkw 0x000000408002220c 0x0000000810004441 0x8811cfc7e81ffe3f 0xd10239f8fd03ffc7

def z1041 : W := mkw 0x034de93540000000 0x0069bd26a8000000 0x400fcdffe0000001 0x0801f9bffc000000

def z1042 : W := mkw 0x036dfb3540000000 0x006dbf66a8000000 0xe0efffffe0000003 0xbc1dfffffc000000

def z1043 : W := mkw 0x130b2c2e1b058543 0x82616585c360b0a8 0xd70f3c7e1f0181c3 0x7ae1e78fc3e03038

def z1044 : W := mkw 0x01022c0819040542 0x00204581032080a8 0xd70e3c381f0007c6 0x7ae1c78703e000f8

def z1045 : W := mkw 0x07dde93540000000 0x00fbbd26a8000000 0xc71fcfffe0000003 0xd8e3f9fffc000000

def z1046 : W := mkw 0x06ddc00006d15000 0x00dbb80000da2a00 0xaff1c0000ffff805 0xd5fe380001ffff00

def z1047 : W := mkw 0x07fdfb3544901000 0x00ffbf66a8920200 0xe7ffffffe0181803 0xfcfffffffc030300

def z1048 : W := mkw 0x07fdfb3540000000 0x00ffbf66a8000000 0xe7fe3fffe0000002 0xfcffc7fffc000000

def z1049 : W := mkw 0x130b286eb307ab4f 0xa261650dd660f569 0x570ff07ff707f9c1 0x2ae1fe0ffee0ff38

def z1050 : W := mkw 0x130b282c13050142 0x826165058260a028 0xd70e3038170601c5 0x3ae1c60702e0c038

def z1051 : W := mkw 0x080204cabefffeff 0x6100409957dfffdf 0x180000001ffffffc 0x0300000003ffffff

def z1052 : W := mkw 0x249004800db805b0 0x0492009001b700b6 0xbff00f801ff807fe 0xf7fe01f003ff00ff

def z1053 : W := mkw 0x130b2c6e1b078747 0x8261658dc360f0e8 0xd70f3c7e170007c3 0x7ae1e78fc2e000f8

def z1054 : W := mkw 0x130b2c6e1b078747 0x8261658dc360f0e8 0x570f3c3e1f0787c4 0x6ae1e787c3e0f0f8

def z1055 : W := mkw 0x06dfc00016d55000 0x00dbf80002daaa00 0xffffcd867ffff805 0xfffff9b0cfffff00

def z1056 : W := mkw 0x130b2c6e1b47c747 0x8261658dc368f8e8 0xdf0f3c7e1fe7e7c7 0x7be1e78fc3fcfcf8

def z1057 : W := mkw 0x08669359d06662ee 0x410cd26b3a0ccc5d 0xf8eeb3f9f0e667ff 0xbf1dd67f3e1cccff

def z1058 : W := mkw 0x0cf4d6d3acfafebd 0x619e9ada759f5fd7 0xa8f1cfc7e8fffe3f 0xd51e39f8fd1fffc7

def z1059 : W := mkw 0x0309282401000100 0x0061250480200020 0xd70f3c7e170001c3 0x7ae1e78fc2e00038

def z1060 : W := mkw 0x07fdfb3540000000 0x00ffbf66a8000000 0xe7ffffffe8078007 0xfcfffffffd00f000

def z1061 : W := mkw 0x036dba3500000000 0x006db746a0000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z1062 : W := mkw 0x08669219106440e2 0x410cd243220c881c 0x78ee303810e007fc 0x2f1dc607021c00ff

def z1063 : W := mkw 0x130b2c6ebb07af4f 0xa261658dd760f5e9 0xd71fffffff07ffc7 0xfae3ffffffe0fff8

def z1064 : W := mkw 0x130b2cee3b0f8f57 0xa261659dc761f1ea 0xdf1f7ffe7f1f9fff 0xfbe3efffcfe3f3ff

def z1065 : W := mkw 0x25b03f800db805b0 0x04b607f001b700b6 0xbfe03c001ff807fe 0x77fc078003ff00ff

def z1066 : W := mkw 0x000004caa80aae5f 0x20000099550155cb 0x8811ffffe81fffff 0xd1023ffffd03ffff

def z1067 : W := mkw 0x07b97b3540000000 0x00f72f66a8000000 0xc71f7fffe0000003 0x78e3effffc000000

def z1068 : W := mkw 0x05b03e000db005a0 0x00b607c001b600b4 0xbff03e001ff807fe 0xf7fe07c003ff00ff

def z1069 : W := mkw 0x07dde93540000000 0x00fbbd26a8000000 0xc71ffdffe0000003 0x78e3ffbffc000000

def z1070 : W := mkw 0x08669259906662ee 0x410cd24b320ccc5d 0x70ee303810e007f8 0x2e1dc607021c00ff

def z1071 : W := mkw 0x130b282c13050142 0x826165058260a028 0x570f307e170001c1 0x2ae1e60fc2e00038

def z1072 : W := mkw 0x07fdfb3540000000 0x00ffbf66a8000000 0x67ff7fffe0000002 0x6cffeffffc000000

def z1073 : W := mkw 0x08669259906662ee 0x410cd24b320ccc5d 0xf8efb27998e7e7ff 0xff1df64f331cfcff

def z1074 : W := mkw 0x024dc03540000000 0x0049b806a8000000 0x400fcfffe0000003 0x0801f9fffc000000

def z1075 : W := mkw 0x0492000016d55000 0x0092400002daaa00 0x3fe000001ffff804 0x27fc000003ffff00

def z1076 : W := mkw 0x25b03f800db805b0 0x04b607f001b700b6 0xbff0bf801ffe67ff 0xf7fe17f003ffccff

def z1077 : W := mkw 0x27fdfb3545b001a0 0x04ffbf66a8b60034 0xfffffffffff801c7 0xffffffffffff0038

def z1078 : W := mkw 0x25b03f822db88db1 0x24b607f045b711b6 0xbff03f801ff99ffe 0xf7fe07f003ff33ff

def z1079 : W := mkw 0x08669259906662ee 0x410cd24b320ccc5d 0x68eeb27980e667fb 0x8d1dd64f301cccff

def z1080 : W := mkw 0x000000c2a00aaa1d 0x2000001854015543 0x8811cfc7e01ff83b 0xd10239f8fc03ff07

def z1081 : W := mkw 0x04d4c00004d05000 0x009a9800009a0a00 0xbff1c0001ffff805 0xf7fe380003ffff00

def z1082 : W := mkw 0x120b006e12078247 0x8241600dc240f048 0xd70f307e1f0787c7 0x7ae1e60fc3e0f0f8

def z1083 : W := mkw 0x0a4fc05bb247fa4f 0x6149f80b7648ff49 0x400fc07fe007f801 0x0801f80ffc00ff00

def z1084 : W := mkw 0x0164bb3540000000 0x002c9766a8000000 0x60ee3fffe0000002 0x2c1dc7fffc000000

def z1085 : W := mkw 0x06dfc00016d55000 0x00dbf80002daaa00 0xfffe00001ffff804 0xffffc00003ffff00

def z1086 : W := mkw 0x08669259906662ee 0x410cd24b320ccc5d 0xf8eff27ff0e667ff 0xbf1dfe4ffe1cccff

def z1087 : W := mkw 0x130b2c6ebb07af4f 0xa261658dd760f5e9 0xd70f3c7e1f07ffc7 0x7ae1e78fc3e0fff8

def z1088 : W := mkw 0x07fdfb3540000000 0x00ffbf66a8000000 0xefffffffe000063f 0xfdfffffffc0000c7

def z1089 : W := mkw 0x0164bb3540000000 0x002c9766a8000000 0x400ebfffe0000003 0x0801d7fffc000000

def z1090 : W := mkw 0x25b03f800db805b0 0x04b607f001b700b6 0xbff17f801ff99ffe 0xf7fe2ff003ff33ff

def z1091 : W := mkw 0x25b03f910db805b0 0x04b607f221b700b6 0xbff03ff99ff807fe 0xf7fe07ff33ff00ff

def z1092 : W := mkw 0x130b2c6ebb07af4f 0xa261658dd760f5e9 0xdf1ffc7fff1fffc7 0xfbe3ff8fffe3fff8

def z1093 : W := mkw 0x24b0138004b800b0 0x0496027000970016 0xbff033801ff807fe 0xf7fe067003ff00ff

def z1094 : W := mkw 0x07fdfb3540000000 0x00ffbf66a8000000 0xe7ffffffe8199803 0xfcfffffffd033300

def z1095 : W := mkw 0x06dfc00016d55000 0x00dbf80002daaa00 0xffffc2001ffffe3f 0xfffff84003ffffc7

def z1096 : W := mkw 0x25b07f804db805b0 0x04b60ff009b700b6 0xbff07f807ff807fe 0xf7fe0ff00fff00ff

def z1097 : W := mkw 0x07fdfb3546911000 0x00ffbf66a8d22200 0xfffffffffff99807 0xffffffffffff3300

def z1098 : W := mkw 0x25b03f800db805b0 0x04b607f001b700b6 0x3ff03f8017f807fa 0xa7fe07f002ff00ff

def z1099 : W := mkw 0x06dfc03556d55000 0x00dbf806aadaaa00 0xffffc0381ffff805 0xfffff80703ffff00

def z1100 : W := mkw 0x00669211106440a0 0x000cd242220c8814 0xf8eeb27990e667ff 0xbf1dd64f321cccff

def z1101 : W := mkw 0x06fdd33540000000 0x00dfba66a8000000 0xe0ffcfffe0000003 0xdc1ff9fffc000000

def z1102 : W := mkw 0x07fdfb3542011000 0x00ffbf66a8402200 0xe7ffffffe0019803 0xfcfffffffc003300

def z1103 : W := mkw 0x130b2c6e1b078747 0x8261658dc360f0e8 0xd70f30381f0787c5 0x7ae1e60703e0f0f8

def z1104 : W := mkw 0x25b03f800db805b0 0x04b607f001b700b6 0x3ff03d801ff807fc 0x67fe07b003ff00ff

def z1105 : W := mkw 0x2cf4939104f840b0 0x459e9272209f0816 0x28f0038000f80038 0x851e0070001f0007

def z1106 : W := mkw 0x06dfc01116d55000 0x00dbf80222daaa00 0xffffc0799ffff805 0xfffff80f33ffff00

def z1107 : W := mkw 0x25b03f800db805b0 0x04b607f001b700b6 0x3fe03f801ff807fe 0x27fc07f003ff00ff

def z1108 : W := mkw 0x030b2c241b050500 0x006165848360a0a0 0xd70f3c7e1f0787c7 0x7ae1e78fc3e0f0f8

def z1109 : W := mkw 0x25902d800db805b0 0x04b205b001b700b6 0xbff00d801ff807fc 0xf7fe01b003ff00ff

def z1110 : W := mkw 0x25b03f820db885b1 0x04b607f041b710b6 0xbff13f861ff987fe 0xf7fe27f0c3ff30ff

def z1111 : W := mkw 0x07fdfb35402000a0 0x00ffbf66a8040014 0xf7fffffff0e001c3 0xfefffffffe1c0038

def z1112 : W := mkw 0x08669259906662ee 0x410cd24b320ccc5d 0xf8fffffff8ffffff 0xff1fffffff1fffff

def z1113 : W := mkw 0x130b2c6e1b078747 0x8261658dc360f0e8 0xd70ffc7fff0787c7 0x7ae1ff8fffe0f0f8

def z1114 : W := mkw 0x25b03f802db80db0 0x24b607f005b701b6 0xbff07f807ff81ffe 0xf7fe0ff00fff03ff

def z1115 : W := mkw 0x130b2ceebb0faf5f 0xa261659dd761f5eb 0xdf1ffc7e1f1fffff 0xfbe3ff8fc3e3ffff

def z1116 : W := mkw 0x05f4bb3540000000 0x00be9766a8000000 0xe7febfffe0000003 0xfcffd7fffc000000

def z1117 : W := mkw 0x0cf4d291a4f878b8 0x619e9a52349f0f17 0x28f0c381e0f87838 0x851e18703c1f0f07

def z1118 : W := mkw 0x130b2c6e1b078747 0x8261658dc360f0e8 0xd70f3fffff0787c7 0x7ae1e7ffffe0f0f8

def z1119 : W := mkw 0x120b044a1b078747 0x824160894360f0e8 0xd70f30781f0787c7 0x7ae1e60f03e0f0f8

def z1120 : W := mkw 0x130b2ceebb0faf5f 0xa261659dd761f5eb 0xdf1f3ffe1f1fffff 0xfbe3e7ffc3e3ffff

def z1121 : W := mkw 0x25b03f800db805b0 0x04b607f001b700b6 0xbff13fc61ff807ff 0xf7fe27f8c3ff00ff

def z1122 : W := mkw 0x25b03fb54db805b0 0x04b607f6a9b700b6 0xbff03fb81ff807fe 0xf7fe07f703ff00ff

def z1123 : W := mkw 0x24f4d39144f850b0 0x049e9a72289f0a16 0x28f0c381e0f87838 0x851e18703c1f0f07

def z1124 : W := mkw 0x13092c6e0b038747 0x8261258dc16070e8 0xc70f3c7e0f0187c3 0x78e1e78fc1e030f8

def z1125 : W := mkw 0x06dfc00016d55000 0x00dbf80002daaa00 0x3ff1c0001ffff804 0xc7fe380003ffff00

def z1126 : W := mkw 0x1a4fc07fd247e24f 0xc349f80ffa48fc49 0x400fc07fe007e001 0x0801f80ffc00fc00

def z1127 : W := mkw 0x25b03f822db88db1 0x24b607f045b711b6 0xbff03f867ff807fe 0xf7fe07f0cfff00ff

def z1128 : W := mkw 0x130b282c13050142 0x826165058260a028 0x570e30381f0781c4 0x2ae1c60703e0f038

def z1129 : W := mkw 0x25b03f800db805b0 0x04b607f001b700b6 0xfffe3ff81ff807ff 0xffffc7ff03ff00ff

def z1130 : W := mkw 0x00000482a808ac19 0x2000009055011583 0x8811cf87e81ff83d 0xd10239f0fd03ff07

def z1131 : W := mkw 0x25b03f800db805b0 0x04b607f001b700b6 0xbff17f867ff807fe 0xf7fe2ff0cfff00ff

def z1132 : W := mkw 0x130b2cae3b0d8d53 0xa2616595c761b1aa 0x571f7dbe7f1999c0 0x6ae3efb7cfe33338

def z1133 : W := mkw 0x2cf4931104f040a0 0x459e9262209e0814 0x20e0000000e00000 0x041c0000001c0000

def z1134 : W := mkw 0x000004c2a80aae1d 0x20000098550155c3 0xc81fffffe81ffe3f 0xf903fffffd03ffc7

def z1135 : W := mkw 0x130b2cee1b0f8757 0x8261659dc361f0ea 0xd70f3ffe1f0787ff 0x7ae1e7ffc3e0f0ff

def z1136 : W := mkw 0x1866925b9267e2ef 0xc30cd24b724cfc5d 0xf8eeb27990e7e7ff 0xbf1dd64f321cfcff

def z1137 : W := mkw 0x130b286c9307234e 0x8261650d9260e469 0xdf0eb279970667ff 0xbbe1d64f32e0ccff

def z1138 : W := mkw 0x08649259806262ee 0x410c924b300c4c5d 0xe8eeb27980e067fb 0xbd1dd64f301c0cff

def z1139 : W := mkw 0x130b2cee1b0f8757 0x8261659dc361f0ea 0xdf1fffffff1f87ff 0xfbe3ffffffe3f0ff

def z1140 : W := mkw 0x130b286e13078347 0x8261650dc260f068 0xd70f307e1f0781c5 0x7ae1e60fc3e0f038

def z1141 : W := mkw 0x0699400006911000 0x00d3280000d22200 0xbff1c0001ffff805 0xf7fe380003ffff00

def z1142 : W := mkw 0x27996da44f991510 0x04f32db489f322a2 0x07114d866f199800 0x40e229b0cde33300

def z1143 : W := mkw 0x130b2c2c1b050542 0x826165858360a0a8 0xd70f3c381f0787c7 0x7ae1e78703e0f0f8

def z1144 : W := mkw 0x25b03fb54db805b0 0x04b607f6a9b700b6 0xbff1fffffff807ff 0xf7fe3fffffff00ff

def z1145 : W := mkw 0x08669259906662ee 0x410cd24b320ccc5d 0xf8fef3f9f0e667ff 0xbf1fde7f3e1cccff

def z1146 : W := mkw 0x07fdfb3540000000 0x00ffbf66a8000000 0xfffffffff0e00007 0xfffffffffe1c0000

def z1147 : W := mkw 0x25b03f822db88db1 0x24b607f045b711b6 0xbff1ff867fffffff 0xf7fe3ff0cfffffff

def z1148 : W := mkw 0x130b286e13078347 0x8261650dc260f068 0x570e3038170781c0 0x2ae1c60702e0f038

def z1149 : W := mkw 0x0cf4d21104f050a0 0x419e9a42209e0a14 0x28f0c00000f87800 0x851e1800001f0f00

def z1150 : W := mkw 0x07fdfb3544900000 0x00ffbf66a8920000 0xefffffffe0f80003 0xfdfffffffc1f0000

def z1151 : W := mkw 0x08669259906662ee 0x410cd24b320ccc5d 0xf8efbe7f90e667ff 0xff1df7cff21cccff

def z1152 : W := mkw 0x020b000812050042 0x004160010240a008 0x570e3038170001c0 0x2ae1c60702e00038

def z1153 : W := mkw 0x08669259926762ee 0x410cd24b324cec5d 0xf8eeb2799fe7e7ff 0xbf1dd64f33fcfcff

def z1154 : W := mkw 0x024f800016d55000 0x0049f00002daaa00 0xffef80001ffff805 0xfffdf00003ffff00

def z1155 : W := mkw 0x24f4d31144b000a0 0x049e9a6228960014 0x20e0000000e00000 0x041c0000001c0000

def z1156 : W := mkw 0x2cf4931184f060a8 0x459e9262309e0c15 0x28e0820180e06038 0x851c1040301c0c07

def z1157 : W := mkw 0x130b282c13050142 0x826165058260a028 0xd70e3038170007c6 0x3ae1c60702e000f8

def z1158 : W := mkw 0x0102280811040142 0x0020450102208028 0x570e3038170001c0 0x2ae1c60702e00038

def z1159 : W := mkw 0x000004c2a80aae1d 0x20000098550155c3 0xb8f1cfc7f8fffe3f 0xf71e39f8ff1fffc7

def z1160 : W := mkw 0x08669259906662ee 0x410cd24b320ccc5d 0xf8fef27990fe7fff 0xbf1fde4f321fcfff

def z1161 : W := mkw 0x07fdfb3540000000 0x00ffbf66a8000000 0xefffffffe8180007 0xfdfffffffd030000

def z1162 : W := mkw 0x08669259906662ee 0x410cd24b320ccc5d 0xf8ee323810e667fe 0xbf1dc647021cccff

def z1163 : W := mkw 0x04b0120004b000a0 0x0096024000960014 0xbfe0320017e007fe 0xb7fc064002fc00ff

def z1164 : W := mkw 0x06dfc00016d55000 0x00dbf80002daaa00 0x77ffc0001ffff801 0x6efff80003ffff00

def z1165 : W := mkw 0x130b282c13050142 0x826165058260a028 0x570f30381f0181c0 0x6ae1e60703e03038

def z1166 : W := mkw 0x07fdfb3540405000 0x00ffbf66a8080a00 0xe7ffffffe0007803 0xfcfffffffc000f00

def z1167 : W := mkw 0x0044801100000000 0x0008900220000000 0xc01fcfffe0000003 0xd803f9fffc000000

def z1168 : W := mkw 0x08669259906662ee 0x410cd24b320ccc5d 0x70eeb27990e667fb 0x2e1dd64f321cccff

def z1169 : W := mkw 0x06dfc00016d55000 0x00dbf80002daaa00 0x7fff40001ffff804 0x6fffe80003ffff00

def z1170 : W := mkw 0x03092c6609028705 0x0061258cc12050e0 0xd70f3c7e1f0787c7 0x7ae1e78fc3e0f0f8

def z1171 : W := mkw 0x000004c2a80aae1d 0x20000098550155c3 0x9f11cfc7ff1ffe3f 0xf3e239f8ffe3ffc7

def z1172 : W := mkw 0x08669259906662ee 0x410cd24b320ccc5d 0x78eeb23990e667fc 0xaf1dd647321cccff

def z1173 : W := mkw 0x130b282c13050142 0x826165058260a028 0x570f3038170781c1 0x2ae1e60702e0f038

def z1174 : W := mkw 0x130b2c6e9b07a74f 0x8261658dd360f4e9 0xd70f3e7f9f0787ff 0x7ae1e7cff3e0f0ff

def z1175 : W := mkw 0x130b2ceebb0faf5f 0xa261659dd761f5eb 0xd70fffffff07ffff 0x7ae1ffffffe0ffff

def z1176 : W := mkw 0x04d6800016d55000 0x009ad00002daaa00 0xfffe80001ffff805 0xffffd00003ffff00

def z1177 : W := mkw 0x069b000016d55000 0x00d3600002daaa00 0xffff00001ffff805 0xffffe00003ffff00

def z1178 : W := mkw 0x0866d259906672ee 0x410cda4b320cce5d 0xf8eef27990e67fff 0xbf1dde4f321ccfff

def z1179 : W := mkw 0x0490000004b000a0 0x0092000000960014 0xbff000001ff807fc 0xf7fe000003ff00ff

def z1180 : W := mkw 0x07fdfb3540000000 0x00ffbf66a8000000 0xf7fffffff00007c7 0xfefffffffe0000f8

def z1181 : W := mkw 0x05f4fb3540000000 0x00be9f66a8000000 0xe0feffffe0000003 0xbc1fdffffc000000

def z1182 : W := mkw 0x0866925bb066eaef 0x610cd24b760cdd5d 0xf8fffffff0e7ffff 0xff1ffffffe1cffff

def z1183 : W := mkw 0x25b03f800db805b0 0x04b607f001b700b6 0xb7f03f8017e007fa 0xf6fe07f002fc00ff

def z1184 : W := mkw 0x07fdfb3540000000 0x00ffbf66a8000000 0xe7ffffffe007f803 0xfcfffffffc00ff00

def z1185 : W := mkw 0x020b000812050042 0x004160010240a008 0xd70f30381f0781c5 0x7ae1e60703e0f038

def z1186 : W := mkw 0x130b282c13050142 0x826165058260a028 0xd70f3c7e1f0781c7 0x7ae1e78fc3e0f038

def z1187 : W := mkw 0x24f4d39144b800b0 0x049e9a7228970016 0x28f0038000f80038 0x851e0070001f0007

def z1188 : W := mkw 0x020b04caba0fae5f 0x204160995741f5cb 0xdf1fffffff1fffff 0xfbe3ffffffe3ffff

def z1189 : W := mkw 0x06dfc00016d55000 0x00dbf80002daaa00 0xfffff0781ffff807 0xfffffe0f03ffff00

def z1190 : W := mkw 0x07fdfb3540000000 0x00ffbf66a8000000 0x471fffffe0000003 0x48e3fffffc000000

def z1191 : W := mkw 0x08669259906662ee 0x410cd24b320ccc5d 0x78ee327990e667fe 0x2f1dc64f321cccff

def z1192 : W := mkw 0x130b286c13070346 0x8261650d8260e068 0xd70f30781f0787c7 0x7ae1e60f03e0f0f8

def z1193 : W := mkw 0x0cf4921184f060a8 0x419e9242309e0c15 0x28f0820180f86038 0x851e1040301f0c07

def z1194 : W := mkw 0x06dfc00016d55000 0x00dbf80002daaa00 0xffffcf801ffff807 0xfffff9f003ffff00

def z1195 : W := mkw 0x130b2c2e1b058543 0x82616585c360b0a8 0xd70f3c3e1f0187c6 0x7ae1e787c3e030f8

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(1,[z0,z1,z2,z3,z4,z5]),(0,[z0,z6,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z8,z7,z5]),(0,[z0,z9,z1,z2,z3,z7,z5])],[(0,[z0,z1,z2,z10,z3,z7,z5]),(0,[z0,z1,z2,z3,z11,z7,z5]),(0,[z0,z12,z1,z2,z13,z3,z5]),(0,[z14,z0,z1,z2,z3,z7,z5])],[(0,[z0,z1,z2,z3,z15,z7,z5]),(0,[z0,z1,z2,z3,z16,z17,z5]),(0,[z0,z18,z19,z1,z2,z7,z5]),(0,[z0,z1,z2,z3,z20,z7,z5])],[(0,[z0,z21,z1,z2,z22,z7,z5]),(0,[z0,z23,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z24,z5]),(0,[z25,z0,z1,z2,z3,z7,z5]),(0,[z0,z26,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z27])],[(0,[z0,z28,z1,z2,z3,z7,z5]),(0,[z29,z0,z1,z2,z3,z30,z5]),(0,[z0,z31,z1,z2,z3,z16,z5]),(0,[z0,z1,z32,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z33,z5]),(0,[z0,z1,z2,z3,z34,z7,z5]),(0,[z0,z35,z1,z36,z3,z7,z5]),(0,[z0,z19,z1,z3,z8,z7,z5]),(0,[z0,z31,z1,z2,z3,z37,z5])],[(1,[z38,z1,z39,z3,z7,z5]),(0,[z38,z1,z2,z39,z3,z7,z5]),(0,[z0,z40,z1,z3,z41,z7,z5]),(0,[z42,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z43,z5]),(0,[z0,z44,z1,z2,z3,z7,z45]),(0,[z0,z1,z2,z3,z7,z5,z46])],[(0,[z0,z1,z2,z3,z7,z5,z47]),(0,[z0,z48,z1,z2,z49,z7,z5]),(0,[z0,z50,z1,z2,z3,z51,z5]),(0,[z0,z1,z52,z2,z3,z7,z5]),(0,[z0,z18,z1,z53,z3,z7,z5])],[(0,[z0,z54,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z55,z5]),(0,[z0,z56,z1,z2,z3,z7,z5])]],
   [[(1,[z0,z1,z2,z3,z7,z5]),(0,[z38,z0,z19,z1,z3,z7,z5]),(0,[z0,z1,z2,z57,z3,z7,z5]),(0,[z0,z1,z2,z3,z58,z59,z5]),(0,[z60,z0,z1,z2,z3,z7,z5]),(0,[z0,z61,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z62,z7,z5]),(0,[z0,z1,z2,z63,z3,z7,z64])],[(1,[z0,z65,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z7,z66,z5])],[(0,[z0,z67,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z68,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z69,z5]),(0,[z70,z0,z1,z2,z3,z58,z5]),(0,[z0,z71,z12,z1,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z72]),(0,[z0,z35,z1,z2,z63,z3,z7]),(0,[z0,z1,z2,z73,z3,z7,z5])],[(0,[z74,z0,z75,z2,z3,z7,z5]),(1,[z0,z1,z2,z3,z76,z5]),(1,[z77,z1,z2,z78,z7,z5]),(0,[z0,z1,z2,z3,z7,z79,z5]),(1,[z0,z80,z81,z3,z7,z5]),(0,[z82,z0,z1,z2,z3,z7,z5]),(0,[z83,z0,z1,z2,z3,z7,z5])],[(0,[z0,z1,z84,z2,z3,z7,z5]),(0,[z0,z1,z85,z2,z3,z7,z5])],[(0,[z0,z1,z2,z3,z7,z86,z5]),(0,[z0,z87,z1,z2,z3,z16,z5]),(1,[z0,z50,z2,z3,z88,z5])],[(0,[z0,z1,z2,z3,z89,z7,z5]),(0,[z0,z1,z81,z3,z37,z7,z5]),(0,[z0,z12,z1,z2,z3,z7,z5]),(0,[z0,z1,z90,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z91,z5])],[(0,[z0,z92,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z93,z5]),(0,[z0,z1,z2,z3,z7,z5,z94]),(0,[z0,z95,z1,z2,z3,z7,z5]),(0,[z0,z18,z1,z2,z63,z7,z5])]],
   [[(0,[z0,z0,z1,z2,z3,z58,z5]),(0,[z0,z1,z2,z3,z7,z59,z5]),(0,[z0,z1,z2,z3,z7,z96,z5]),(0,[z0,z1,z2,z3,z7,z5,z97])],[(0,[z98,z0,z1,z2,z99,z7,z5]),(0,[z0,z1,z2,z3,z100,z7,z5]),(0,[z0,z1,z2,z3,z101,z7,z5]),(0,[z0,z80,z1,z81,z3,z7,z5]),(0,[z0,z1,z2,z3,z102,z7,z5]),(0,[z0,z103,z1,z2,z3,z104,z5]),(0,[z0,z1,z2,z3,z7,z105,z5]),(0,[z0,z1,z2,z106,z3,z7,z5])],[(0,[z0,z1,z2,z107,z3,z7,z5]),(0,[z0,z1,z2,z108,z41,z7,z5]),(0,[z0,z1,z2,z3,z7,z109,z5]),(0,[z110,z0,z1,z2,z3,z7,z5]),(0,[z0,z18,z1,z2,z111,z7,z5])],[(0,[z0,z1,z112,z2,z3,z16,z5]),(0,[z0,z1,z2,z3,z7,z113,z5]),(0,[z0,z114,z1,z2,z3,z7,z115]),(0,[z0,z1,z2,z3,z7,z5,z116])],[(0,[z0,z1,z2,z3,z117,z7,z5])],[(0,[z0,z1,z2,z3,z16,z118,z5]),(0,[z0,z119,z1,z2,z3,z16,z5]),(0,[z0,z1,z2,z3,z7,z16,z5]),(0,[z120,z0,z1,z2,z3,z121,z5]),(0,[z0,z122,z1,z2,z3,z7,z5]),(0,[z0,z65,z1,z2,z3,z7,z5])],[(0,[z123,z0,z1,z2,z3,z7,z5]),(0,[z74,z0,z35,z2,z3,z7,z5]),(0,[z124,z0,z1,z2,z3,z7,z5]),(0,[z125,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z78,z7,z64,z5]),(0,[z0,z44,z1,z2,z3,z16,z5]),(0,[z0,z1,z2,z3,z126,z49,z7]),(0,[z127,z0,z1,z2,z3,z7,z5])],[(0,[z0,z128,z1,z2,z3,z7,z5]),(0,[z0,z1,z129,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z130,z5]),(0,[z0,z1,z2,z3,z7,z5,z131])]],
   [[(0,[z0,z1,z132,z3,z41,z7,z5]),(0,[z0,z48,z1,z2,z3,z7,z5]),(0,[z0,z133,z31,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z134,z7,z5]),(1,[z98,z75,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z41,z58,z5]),(0,[z0,z1,z2,z3,z16,z135,z5]),(0,[z0,z1,z2,z3,z7,z5,z136]),(0,[z0,z1,z2,z3,z7,z115,z5]),(0,[z0,z1,z2,z3,z137,z7,z5])],[(0,[z0,z1,z2,z3,z16,z5,z138]),(0,[z0,z1,z2,z3,z139,z7,z5]),(0,[z0,z1,z2,z3,z7,z140,z91]),(0,[z0,z1,z2,z3,z7,z141,z5])],[(1,[z0,z142,z2,z3,z7,z5]),(0,[z0,z18,z1,z2,z3,z16,z5]),(0,[z0,z1,z2,z3,z58,z143,z5]),(0,[z0,z1,z2,z3,z37,z58,z5]),(0,[z0,z1,z2,z3,z7,z5,z144]),(0,[z0,z114,z31,z1,z3,z7,z5])],[(0,[z0,z145,z1,z2,z3,z7,z5]),(0,[z146,z0,z1,z2,z3,z7,z5]),(0,[z147,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z148,z3,z7,z5]),(1,[z0,z1,z2,z3,z7,z140])],[(0,[z38,z0,z1,z2,z149,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z150]),(0,[z0,z1,z2,z3,z7,z151,z5]),(0,[z1,z2,z78,z3,z41,z7,z5]),(0,[z0,z1,z2,z41,z49,z7,z5]),(1,[z0,z152,z1,z2,z3,z7]),(0,[z0,z1,z112,z3,z7,z5,z45]),(0,[z0,z1,z153,z2,z3,z7,z5]),(0,[z0,z154,z1,z2,z3,z7,z5])],[(0,[z0,z1,z2,z3,z8,z58,z5]),(0,[z0,z1,z2,z3,z58,z17,z5]),(0,[z0,z21,z1,z2,z49,z7,z5]),(0,[z0,z1,z2,z155,z3,z7,z5]),(1,[z0,z87,z1,z2,z91,z5]),(1,[z0,z133,z1,z2,z3,z27])],[(0,[z0,z119,z1,z3,z7,z5,z45]),(1,[z0,z1,z156,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z157,z5])]],
   [[(0,[z158,z0,z1,z2,z3,z7,z5]),(0,[z0,z159,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z160,z3,z16,z5]),(0,[z0,z133,z1,z2,z3,z58,z5]),(0,[z0,z1,z2,z3,z7,z161,z5]),(0,[z0,z162,z1,z2,z3,z7,z5])],[(1,[z0,z1,z2,z149,z7,z5]),(0,[z0,z1,z163,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z164,z45]),(1,[z0,z71,z1,z3,z7,z5]),(0,[z0,z1,z3,z37,z7,z104,z5]),(0,[z0,z165,z1,z2,z3,z7,z5]),(1,[z0,z18,z1,z2,z7,z131])],[(0,[z38,z0,z1,z2,z3,z58,z5]),(0,[z166,z0,z1,z2,z3,z15,z5]),(0,[z0,z1,z2,z3,z7,z167,z5]),(0,[z0,z1,z2,z13,z3,z111,z5])],[(0,[z98,z0,z1,z2,z3,z7,z168]),(1,[z0,z169,z2,z3,z7,z5]),(0,[z42,z0,z1,z2,z3,z58,z5]),(0,[z0,z170,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z171,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z172,z5]),(0,[z0,z87,z1,z2,z7,z91,z5])],[(0,[z0,z65,z1,z2,z3,z49,z5]),(0,[z0,z35,z1,z2,z3,z7,z138]),(0,[z0,z173,z1,z2,z3,z7,z5])],[(0,[z0,z1,z2,z39,z3,z16,z5]),(0,[z0,z174,z1,z2,z3,z58,z5]),(0,[z175,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z176,z5]),(0,[z0,z1,z2,z3,z7,z140,z5]),(0,[z0,z1,z2,z3,z177,z7,z27])],[(1,[z0,z1,z2,z3,z58,z5]),(0,[z0,z1,z2,z3,z7,z178,z5]),(0,[z0,z114,z2,z81,z3,z7,z5])],[(0,[z0,z1,z2,z3,z7,z5,z179]),(0,[z0,z103,z1,z2,z3,z16,z5]),(0,[z120,z1,z2,z3,z7,z143,z5]),(1,[z0,z1,z180,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z181,z5])]],
   [[(0,[z182,z0,z1,z2,z3,z7,z5]),(0,[z42,z1,z2,z3,z7,z16,z5]),(0,[z120,z0,z1,z2,z3,z16,z5]),(0,[z0,z183,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z184]),(0,[z0,z185,z1,z2,z3,z7,z5]),(0,[z186,z0,z1,z2,z3,z7,z5])],[(0,[z74,z0,z2,z3,z7,z187,z5]),(0,[z0,z1,z2,z3,z7,z188,z5]),(0,[z0,z1,z2,z3,z7,z5,z189]),(1,[z0,z1,z112,z108,z7,z5]),(0,[z0,z1,z2,z190,z3,z7,z5]),(0,[z0,z1,z2,z3,z191,z7,z5]),(0,[z0,z1,z2,z3,z7,z192,z5])],[(1,[z0,z1,z3,z193,z16,z5]),(0,[z0,z1,z2,z3,z194,z7,z5]),(0,[z0,z87,z1,z2,z13,z7,z5]),(0,[z0,z195,z1,z2,z3,z7,z5])],[(0,[z74,z0,z1,z2,z3,z58,z5]),(0,[z0,z1,z2,z3,z7,z196,z5]),(0,[z0,z1,z2,z3,z7,z5,z197]),(0,[z0,z198,z1,z2,z3,z7,z5]),(0,[z0,z199,z1,z2,z3,z7,z5])],[(1,[z0,z200,z1,z3,z7,z5]),(0,[z0,z12,z1,z2,z3,z58,z5]),(0,[z0,z201,z1,z2,z3,z7,z5]),(0,[z0,z202,z1,z2,z3,z7,z5])],[(0,[z0,z1,z2,z3,z7,z203,z5]),(0,[z77,z0,z1,z2,z3,z58,z5]),(0,[z0,z1,z204,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z205]),(0,[z0,z50,z1,z2,z13,z3,z5]),(0,[z0,z18,z206,z1,z2,z3,z7]),(0,[z0,z1,z2,z3,z207,z7,z5])],[(0,[z38,z0,z1,z2,z3,z7,z208]),(0,[z0,z209,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z108,z78,z7,z5]),(0,[z0,z1,z2,z3,z210,z16,z5]),(0,[z0,z1,z2,z3,z7,z211,z5]),(0,[z212,z0,z1,z2,z3,z7,z5]),(0,[z0,z213,z1,z2,z3,z7,z5])],[(0,[z70,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z214]),(0,[z0,z215,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z16,z187,z5]),(0,[z0,z216,z1,z2,z3,z16,z5]),(0,[z0,z1,z2,z3,z217,z7,z5]),(1,[z0,z35,z2,z3,z7,z138]),(0,[z0,z1,z2,z7,z5,z46,z27])]],
   [[(0,[z0,z1,z75,z2,z3,z16,z5]),(1,[z29,z1,z2,z41,z7,z5]),(0,[z0,z21,z1,z2,z3,z7,z5]),(0,[z0,z44,z218,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z219])],[(0,[z0,z1,z2,z3,z220,z7,z5]),(0,[z0,z31,z1,z2,z3,z104,z5])],[(1,[z0,z1,z2,z3,z7,z208]),(1,[z0,z40,z1,z3,z7,z5]),(1,[z0,z1,z132,z3,z7,z5])],[(0,[z0,z221,z222,z2,z3,z7,z5]),(0,[z0,z223,z1,z2,z3,z7,z5]),(0,[z0,z114,z1,z2,z3,z7,z94]),(0,[z0,z1,z2,z3,z224,z7,z5]),(0,[z0,z1,z2,z3,z7,z225,z5]),(0,[z0,z226,z1,z2,z3,z7,z5])],[(0,[z0,z1,z2,z63,z3,z7,z143]),(0,[z0,z1,z2,z3,z227,z7,z5]),(0,[z0,z21,z2,z22,z3,z7,z5]),(0,[z0,z1,z2,z3,z177,z7,z17])],[(0,[z0,z1,z228,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z229,z7,z5]),(1,[z0,z1,z2,z230,z7,z5]),(0,[z0,z1,z2,z3,z7,z231,z5]),(0,[z0,z1,z2,z3,z7,z5,z232])],[(0,[z0,z233,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z30,z7,z5]),(0,[z77,z1,z2,z78,z3,z7,z5]),(0,[z0,z48,z1,z2,z3,z58,z5]),(0,[z0,z1,z2,z3,z58,z5,z138])],[(0,[z0,z1,z2,z234,z3,z7,z5]),(0,[z235,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z236])]],
   [[(0,[z74,z0,z1,z2,z3,z237,z5]),(0,[z166,z1,z238,z2,z3,z7,z5]),(0,[z0,z35,z1,z2,z3,z16,z5]),(0,[z239,z0,z1,z2,z3,z7,z5])],[(0,[z0,z1,z2,z22,z41,z7,z5]),(0,[z0,z1,z2,z3,z240,z7,z5]),(0,[z0,z1,z2,z3,z241,z7,z5])],[(0,[z0,z50,z1,z2,z3,z7,z5]),(0,[z0,z242,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z243,z3,z7,z5]),(0,[z0,z1,z2,z63,z3,z7,z5]),(0,[z0,z18,z1,z2,z7,z5,z131])],[(0,[z0,z244,z1,z2,z3,z7,z5]),(0,[z77,z0,z1,z2,z3,z245,z5]),(0,[z0,z1,z2,z3,z7,z246,z5])],[(1,[z0,z247,z1,z3,z7,z5]),(0,[z0,z114,z1,z3,z37,z7,z5]),(0,[z0,z114,z44,z1,z3,z7,z5]),(1,[z0,z248,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z249,z7,z5])],[(0,[z0,z1,z2,z3,z7,z208,z5]),(1,[z0,z1,z2,z3,z30,z5]),(0,[z250,z0,z1,z2,z3,z7,z5]),(0,[z0,z251,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z252,z3,z7,z5]),(0,[z0,z1,z2,z253,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z254,z5]),(0,[z0,z1,z2,z3,z7,z255,z5]),(0,[z0,z1,z3,z7,z181,z5,z45]),(0,[z0,z44,z1,z3,z7,z181,z5]),(0,[z0,z256,z1,z2,z3,z7,z5])],[(1,[z0,z31,z1,z3,z104,z5])],[(0,[z0,z1,z2,z3,z16,z5,z257]),(0,[z0,z1,z2,z3,z58,z258,z5]),(0,[z0,z259,z1,z2,z3,z7,z5]),(0,[z0,z247,z1,z3,z7,z143,z5]),(0,[z0,z221,z114,z2,z3,z7,z5]),(1,[z0,z1,z2,z63,z7,z64])]],
   [[(0,[z0,z1,z2,z3,z7,z187,z164]),(0,[z0,z1,z2,z3,z7,z260,z5]),(0,[z0,z261,z1,z2,z3,z7,z5])],[(0,[z0,z262,z1,z2,z3,z7,z5]),(0,[z0,z263,z1,z2,z3,z7,z5]),(0,[z0,z221,z114,z1,z3,z7,z5]),(0,[z0,z1,z2,z3,z264,z7,z5]),(0,[z265,z0,z1,z2,z3,z7,z5]),(0,[z266,z0,z1,z2,z3,z7,z5])],[(0,[z166,z0,z1,z39,z3,z7,z5]),(0,[z0,z1,z2,z3,z51,z58,z5]),(0,[z120,z267,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z268,z5]),(0,[z0,z1,z2,z3,z269,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z270]),(0,[z0,z206,z1,z2,z3,z7,z181])],[(0,[z0,z222,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z271]),(0,[z0,z272,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z273,z3,z7,z5])],[(0,[z29,z0,z1,z2,z3,z16,z5]),(0,[z274,z0,z1,z2,z3,z7,z5]),(0,[z0,z275,z1,z2,z3,z7,z5]),(0,[z0,z9,z1,z2,z7,z5,z45]),(0,[z0,z1,z2,z3,z7,z5,z276])],[(0,[z0,z277,z1,z2,z3,z16,z5]),(0,[z0,z133,z1,z2,z3,z7,z5])],[(0,[z98,z0,z1,z2,z3,z16,z5]),(0,[z267,z1,z2,z3,z7,z5,z164]),(0,[z0,z2,z3,z51,z7,z88,z5]),(1,[z0,z19,z1,z8,z7,z5]),(0,[z0,z31,z1,z3,z7,z104,z5]),(0,[z0,z278,z1,z2,z3,z7,z5])],[(0,[z38,z0,z1,z2,z3,z7,z5]),(0,[z29,z0,z1,z2,z41,z7,z5]),(0,[z0,z1,z2,z3,z7,z258,z5]),(0,[z0,z279,z1,z2,z3,z7,z5]),(0,[z0,z119,z1,z2,z3,z7,z45]),(0,[z0,z1,z2,z280,z3,z7,z5])]],
   [[(0,[z0,z1,z2,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z58,z281,z5]),(0,[z0,z87,z50,z1,z2,z3,z5]),(0,[z0,z1,z156,z2,z3,z7,z5])],[(0,[z0,z75,z2,z81,z3,z7,z5]),(0,[z0,z221,z75,z2,z3,z7,z5]),(0,[z282,z0,z1,z2,z3,z7,z5]),(0,[z267,z0,z1,z2,z3,z58,z5]),(0,[z0,z283,z1,z2,z3,z7,z5]),(1,[z0,z1,z36,z3,z7,z5]),(0,[z0,z87,z1,z2,z3,z91,z5]),(0,[z0,z1,z2,z13,z111,z7,z5]),(0,[z0,z133,z1,z2,z63,z3,z7])],[(0,[z0,z1,z2,z284,z3,z7,z5]),(0,[z0,z174,z1,z2,z3,z7,z5]),(0,[z285,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z286,z7,z5]),(1,[z0,z103,z1,z3,z37,z5]),(0,[z0,z287,z1,z2,z3,z7,z5])],[(0,[z0,z1,z2,z78,z3,z16,z5]),(0,[z0,z1,z2,z3,z58,z187,z5]),(0,[z0,z206,z35,z2,z3,z7,z5]),(0,[z0,z1,z288,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z289]),(0,[z0,z133,z1,z2,z3,z177,z5])],[(0,[z98,z0,z1,z2,z290,z7,z5]),(0,[z0,z1,z2,z3,z49,z58,z5]),(0,[z0,z291,z1,z2,z3,z7,z5]),(0,[z0,z19,z1,z2,z3,z7,z5]),(0,[z0,z1,z218,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z292,z5])],[(0,[z0,z1,z2,z3,z7,z293,z5])],[(0,[z0,z1,z294,z2,z3,z7,z5]),(0,[z146,z0,z1,z2,z3,z16,z5]),(0,[z0,z21,z1,z2,z3,z58,z5]),(0,[z0,z263,z2,z3,z7,z5,z164]),(0,[z0,z1,z2,z3,z177,z17,z5])],[(0,[z295,z0,z1,z2,z3,z7,z5]),(0,[z98,z0,z1,z2,z3,z134,z5]),(0,[z166,z0,z1,z2,z3,z16,z5]),(1,[z120,z1,z2,z3,z7,z143]),(0,[z0,z21,z1,z180,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z296,z5]),(0,[z0,z1,z2,z3,z297,z7,z5])]],
   [[(0,[z74,z0,z1,z2,z3,z7,z5]),(0,[z0,z298,z1,z2,z3,z7,z5]),(0,[z0,z1,z238,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z299,z5]),(0,[z0,z18,z1,z2,z3,z7,z164]),(0,[z0,z1,z2,z3,z300,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z301]),(0,[z0,z1,z2,z302,z3,z7,z5])],[(0,[z0,z1,z2,z303,z3,z7,z5]),(0,[z0,z133,z103,z1,z2,z3,z5]),(0,[z0,z87,z133,z1,z2,z3,z5])],[(0,[z304,z0,z1,z2,z3,z7,z5]),(0,[z77,z0,z1,z2,z3,z7,z5]),(0,[z0,z40,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z13,z3,z16,z5])],[(0,[z0,z1,z2,z78,z8,z7,z5]),(0,[z0,z1,z2,z3,z229,z58,z5]),(0,[z0,z1,z2,z3,z305,z7,z5]),(0,[z0,z306,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z307,z3,z7,z5])],[(0,[z0,z221,z35,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z308])],[(0,[z0,z309,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z4,z5]),(0,[z0,z1,z2,z22,z78,z7,z5]),(0,[z0,z1,z2,z3,z58,z7,z5]),(0,[z1,z2,z3,z58,z7,z16,z5]),(0,[z0,z200,z1,z2,z3,z7,z5])],[(0,[z310,z0,z1,z2,z3,z7,z5]),(0,[z38,z0,z1,z238,z3,z7,z5]),(0,[z38,z0,z1,z108,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z311,z5])],[(0,[z166,z0,z1,z2,z3,z151,z5]),(0,[z0,z1,z312,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z313,z5])]],
   [[(0,[z38,z0,z1,z2,z3,z7,z314]),(0,[z0,z1,z315,z2,z3,z7,z5]),(0,[z0,z1,z2,z63,z3,z58,z5]),(0,[z0,z50,z1,z2,z3,z58,z5]),(0,[z0,z1,z2,z316,z3,z7,z5]),(0,[z0,z18,z1,z112,z2,z7,z5]),(0,[z0,z31,z1,z2,z3,z17,z5])],[(0,[z166,z0,z1,z3,z7,z5,z45]),(0,[z0,z1,z2,z3,z317,z7,z5]),(0,[z0,z44,z1,z3,z8,z7,z5]),(0,[z0,z318,z1,z2,z3,z7,z5])],[(1,[z0,z1,z2,z3,z7,z168]),(0,[z38,z0,z142,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z319,z7,z5]),(0,[z0,z320,z1,z2,z3,z7,z5]),(0,[z0,z18,z1,z2,z3,z7,z131])],[(0,[z0,z1,z2,z3,z321,z7,z5])],[(1,[z0,z1,z2,z3,z7,z314]),(0,[z0,z1,z2,z3,z16,z64,z5]),(0,[z0,z1,z2,z322,z3,z7,z5]),(0,[z120,z0,z1,z2,z10,z7,z5]),(0,[z0,z1,z2,z81,z3,z7,z5]),(0,[z0,z1,z2,z323,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z324])],[(0,[z120,z0,z1,z2,z3,z7,z164]),(0,[z0,z325,z1,z2,z3,z7,z5])],[(0,[z98,z0,z1,z2,z3,z203,z5]),(1,[z166,z1,z238,z3,z7,z5]),(1,[z0,z1,z2,z3,z326,z5]),(0,[z0,z327,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z328,z3,z7,z5]),(0,[z0,z206,z2,z3,z7,z187,z5]),(0,[z0,z1,z112,z2,z8,z7,z5]),(0,[z0,z44,z1,z2,z3,z7,z181])],[(0,[z0,z262,z1,z2,z3,z58,z5]),(0,[z0,z221,z1,z81,z3,z7,z5]),(0,[z0,z329,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z330,z5])]],
   [[(0,[z0,z1,z2,z3,z7,z76,z5]),(0,[z0,z1,z2,z3,z16,z5,z45]),(0,[z0,z1,z2,z3,z177,z58,z5]),(0,[z0,z19,z1,z81,z3,z7,z5]),(0,[z0,z331,z1,z2,z3,z7,z5])],[(0,[z0,z1,z2,z3,z7,z332,z5]),(0,[z0,z222,z1,z2,z3,z58,z5]),(0,[z0,z18,z1,z2,z41,z7,z5]),(0,[z0,z215,z1,z2,z3,z16,z5]),(1,[z0,z1,z2,z3,z333,z5]),(0,[z0,z1,z2,z334,z3,z7,z5]),(0,[z0,z12,z1,z2,z3,z88,z5]),(0,[z0,z87,z1,z2,z3,z17,z5]),(0,[z0,z1,z2,z3,z7,z335,z5])],[(0,[z38,z0,z169,z2,z3,z7,z5]),(0,[z0,z114,z1,z2,z3,z58,z5]),(0,[z0,z1,z2,z3,z305,z49,z5]),(0,[z0,z71,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z336,z3,z7,z5]),(0,[z0,z337,z1,z2,z3,z7,z5])],[(0,[z0,z1,z338,z2,z3,z7,z5]),(0,[z29,z0,z1,z2,z78,z7,z5]),(0,[z0,z1,z2,z339,z3,z7,z5]),(0,[z0,z1,z2,z3,z16,z5,z164]),(0,[z0,z1,z2,z3,z7,z5,z257]),(0,[z0,z1,z2,z3,z7,z5,z5]),(0,[z0,z340,z1,z2,z3,z7,z5]),(0,[z0,z19,z1,z112,z3,z7,z5]),(0,[z0,z1,z108,z3,z8,z7,z5]),(0,[z0,z1,z2,z341,z3,z7,z5])],[(0,[z0,z1,z238,z81,z3,z7,z5]),(0,[z0,z1,z2,z3,z342,z7,z5]),(0,[z0,z1,z2,z3,z111,z16,z5]),(0,[z0,z247,z1,z2,z3,z7,z5]),(1,[z0,z21,z2,z22,z7,z5]),(0,[z0,z1,z2,z3,z343,z7,z5]),(0,[z344,z0,z1,z2,z3,z7,z5]),(0,[z345,z0,z1,z2,z3,z7,z5])],[(0,[z346,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z347,z3,z7,z5]),(0,[z348,z0,z1,z2,z3,z7,z5]),(0,[z0,z349,z1,z2,z3,z7,z5])],[(0,[z0,z350,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z351,z5]),(0,[z0,z1,z2,z149,z3,z7,z5]),(0,[z0,z352,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z143,z5]),(0,[z0,z1,z2,z353,z3,z7,z5])],[(0,[z0,z0,z1,z2,z3,z16,z5]),(0,[z0,z221,z2,z3,z7,z187,z5]),(0,[z0,z1,z2,z354,z3,z7,z5]),(0,[z0,z1,z2,z180,z3,z7,z5]),(0,[z0,z1,z2,z3,z51,z7,z5]),(0,[z0,z103,z1,z3,z37,z7,z5]),(0,[z0,z195,z1,z2,z7,z5,z27])]],
   [[(0,[z0,z1,z2,z3,z7,z355,z5]),(0,[z267,z0,z1,z2,z3,z7,z143]),(0,[z0,z1,z81,z108,z3,z7,z5]),(0,[z356,z0,z1,z2,z3,z7,z5]),(1,[z0,z1,z53,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z357])],[(0,[z0,z221,z1,z2,z3,z58,z5]),(0,[z0,z358,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z17,z5])],[(0,[z0,z1,z2,z3,z193,z16,z5]),(0,[z0,z1,z3,z193,z7,z16,z5]),(0,[z0,z359,z1,z2,z3,z7,z5]),(0,[z0,z19,z1,z2,z3,z58,z5]),(1,[z0,z1,z2,z3,z121,z5]),(0,[z0,z360,z1,z2,z3,z7,z5]),(0,[z0,z361,z35,z1,z3,z7,z5]),(0,[z0,z35,z1,z2,z3,z7,z45]),(0,[z362,z0,z1,z2,z3,z7,z5])],[(0,[z363,z0,z1,z2,z3,z7,z5])],[(0,[z0,z1,z2,z3,z7,z364,z5]),(0,[z0,z1,z2,z3,z7,z5,z365])],[(0,[z0,z366,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z230,z7,z5]),(0,[z367,z0,z1,z2,z3,z7,z5]),(0,[z0,z368,z1,z2,z3,z7,z5])],[(0,[z166,z0,z31,z1,z3,z7,z5]),(0,[z0,z1,z238,z2,z3,z58,z5]),(0,[z267,z0,z1,z2,z3,z7,z5]),(0,[z0,z369,z1,z2,z3,z7,z5]),(0,[z0,z370,z1,z2,z3,z7,z5])],[(0,[z0,z1,z2,z41,z7,z64,z5]),(0,[z0,z1,z2,z3,z7,z371,z5])]],
   [[(0,[z98,z0,z1,z2,z3,z7,z332]),(0,[z372,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z41,z16,z5]),(0,[z0,z373,z1,z2,z3,z7,z5]),(0,[z374,z0,z1,z2,z3,z7,z5]),(0,[z0,z50,z2,z3,z7,z88,z5]),(0,[z0,z1,z2,z3,z375,z7,z5])],[(0,[z376,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z377,z3,z7,z5]),(1,[z0,z2,z3,z7,z178,z5]),(0,[z0,z1,z2,z3,z49,z7,z5]),(0,[z0,z1,z3,z8,z7,z5,z45])],[(0,[z0,z1,z2,z3,z7,z5,z168]),(0,[z0,z1,z2,z132,z3,z7,z5]),(0,[z0,z80,z1,z2,z3,z16,z5]),(0,[z0,z1,z2,z3,z37,z16,z5])],[(0,[z0,z1,z2,z3,z58,z58,z5]),(0,[z0,z1,z2,z378,z3,z7,z5]),(0,[z0,z1,z2,z3,z379,z7,z5]),(0,[z0,z1,z2,z3,z7,z380,z5]),(0,[z0,z1,z2,z3,z7,z5,z381])],[(0,[z0,z1,z2,z3,z7,z5,z314]),(0,[z0,z1,z2,z3,z16,z382,z5]),(0,[z0,z383,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z384,z5]),(0,[z0,z1,z2,z3,z7,z385,z5]),(0,[z0,z18,z1,z2,z3,z7,z64])],[(0,[z0,z386,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z8,z16,z5]),(0,[z0,z1,z2,z108,z3,z58,z5]),(0,[z0,z44,z1,z112,z3,z7,z5])],[(1,[z74,z222,z2,z3,z7,z5]),(0,[z387,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z388,z3,z58,z5]),(0,[z0,z1,z2,z389,z3,z7,z5])],[(1,[z0,z1,z2,z3,z7,z390]),(0,[z391,z0,z1,z2,z3,z7,z5]),(1,[z0,z221,z114,z3,z7,z5]),(0,[z392,z0,z1,z2,z3,z7,z5])]],
   [[(0,[z0,z1,z393,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z58,z64,z5]),(0,[z120,z0,z1,z2,z3,z300,z5]),(0,[z0,z114,z80,z1,z3,z7,z5])],[(0,[z0,z1,z2,z3,z7,z394,z5]),(0,[z0,z395,z1,z2,z3,z7,z5]),(0,[z396,z0,z1,z2,z3,z7,z5]),(0,[z0,z397,z1,z2,z3,z7,z5])],[(0,[z0,z1,z39,z81,z3,z7,z5]),(1,[z0,z1,z2,z3,z109,z5]),(0,[z42,z0,z1,z2,z3,z16,z5]),(0,[z0,z1,z2,z81,z3,z58,z5]),(1,[z0,z12,z2,z3,z51,z5]),(1,[z0,z44,z1,z3,z7,z181]),(0,[z0,z1,z2,z3,z7,z398,z5]),(0,[z0,z1,z2,z63,z7,z64,z5]),(0,[z0,z1,z2,z63,z3,z177,z7]),(0,[z0,z1,z2,z3,z7,z5,z399])],[(0,[z0,z152,z1,z2,z3,z7,z5]),(0,[z0,z103,z1,z2,z3,z17,z5])],[(0,[z0,z169,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z118,z5]),(0,[z0,z1,z2,z3,z58,z5,z45]),(0,[z0,z44,z1,z2,z3,z58,z5]),(0,[z0,z1,z400,z2,z3,z7,z5]),(0,[z0,z206,z1,z2,z3,z7,z187]),(0,[z0,z1,z2,z3,z7,z5,z401]),(0,[z0,z402,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z5,z403,z131]),(0,[z404,z0,z1,z2,z3,z7,z5])],[(0,[z405,z0,z1,z2,z3,z7,z5]),(0,[z0,z18,z1,z2,z78,z7,z5]),(0,[z0,z1,z2,z406,z3,z7,z5]),(1,[z0,z1,z2,z3,z16,z5]),(0,[z0,z1,z2,z3,z407,z58,z5]),(0,[z0,z221,z80,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z408,z5])],[(0,[z77,z0,z1,z2,z3,z7,z390]),(1,[z42,z1,z2,z3,z16,z5]),(0,[z0,z1,z2,z3,z409,z58,z5]),(0,[z0,z1,z2,z22,z3,z7,z5])],[(0,[z0,z1,z2,z3,z410,z7,z5]),(0,[z0,z411,z1,z2,z3,z7,z5]),(0,[z146,z1,z2,z3,z58,z7,z5]),(0,[z0,z1,z2,z3,z58,z5,z164]),(0,[z0,z87,z12,z1,z2,z3,z5])]],
   [[(0,[z0,z1,z2,z3,z7,z135,z5]),(0,[z0,z1,z2,z3,z412,z7,z5])],[(0,[z267,z0,z1,z2,z3,z326,z5]),(0,[z0,z413,z1,z2,z3,z7,z5]),(1,[z0,z1,z2,z3,z305,z5]),(0,[z0,z1,z2,z3,z7,z5,z138]),(0,[z0,z1,z2,z3,z7,z5,z414]),(0,[z0,z1,z2,z3,z7,z415,z5])],[(0,[z74,z0,z1,z2,z3,z16,z5]),(0,[z0,z1,z2,z3,z416,z7,z5])],[(1,[z0,z1,z2,z290,z7,z5]),(0,[z417,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z3,z7,z5]),(0,[z0,z12,z1,z2,z3,z16,z5]),(0,[z0,z1,z2,z418,z3,z7,z5])],[(0,[z98,z0,z1,z338,z3,z7,z5]),(0,[z0,z419,z1,z2,z3,z7,z5]),(0,[z267,z0,z1,z2,z3,z333,z5]),(0,[z0,z1,z2,z3,z7,z143,z138]),(0,[z0,z1,z2,z3,z7,z420,z5])],[(0,[z0,z421,z1,z2,z3,z7,z5]),(1,[z0,z1,z2,z3,z151,z5]),(0,[z0,z206,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z422,z5]),(0,[z0,z1,z2,z3,z423,z7,z5]),(0,[z0,z1,z2,z3,z177,z7,z5])],[(1,[z0,z1,z2,z3,z134,z5]),(0,[z0,z1,z2,z3,z424,z7,z5]),(0,[z0,z1,z2,z3,z425,z7,z5]),(0,[z0,z426,z1,z2,z3,z7,z5])],[(0,[z0,z427,z1,z2,z3,z7,z5]),(0,[z1,z2,z3,z7,z143,z5,z164]),(0,[z0,z114,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z428,z7,z5]),(0,[z0,z429,z1,z2,z3,z7,z5])]],
   [[(0,[z0,z1,z2,z3,z7,z237,z5]),(0,[z0,z1,z2,z3,z7,z430,z5]),(0,[z0,z1,z2,z3,z7,z5,z431]),(0,[z432,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z111,z7,z64,z5]),(0,[z0,z1,z2,z7,z64,z5,z131])],[(0,[z0,z1,z2,z36,z3,z7,z5]),(0,[z0,z206,z1,z2,z63,z3,z7]),(0,[z0,z433,z1,z2,z3,z7,z91])],[(0,[z0,z1,z2,z434,z3,z7,z5]),(0,[z0,z1,z435,z2,z3,z7,z5]),(0,[z0,z436,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z437]),(0,[z0,z438,z1,z2,z3,z7,z5]),(1,[z0,z1,z2,z7,z5,z46])],[(1,[z0,z1,z2,z99,z7,z5]),(0,[z0,z439,z1,z2,z3,z7,z5])],[(0,[z0,z1,z2,z3,z7,z440,z5]),(0,[z0,z441,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z16,z88,z5]),(0,[z0,z19,z1,z2,z7,z64,z5]),(0,[z0,z1,z2,z3,z442,z7,z5])],[(0,[z0,z48,z1,z2,z3,z16,z5]),(0,[z0,z1,z2,z3,z7,z5,z443])],[(0,[z38,z166,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z181,z164]),(0,[z0,z221,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z444,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z445,z5]),(0,[z0,z1,z2,z3,z7,z446,z5]),(0,[z0,z1,z2,z3,z7,z447,z5]),(0,[z0,z448,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z449,z5]),(0,[z0,z1,z2,z13,z3,z91,z5]),(0,[z0,z1,z450,z2,z3,z7,z5])],[(0,[z0,z1,z2,z451,z3,z7,z5]),(0,[z166,z0,z1,z3,z37,z7,z5]),(0,[z166,z0,z44,z1,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z390]),(0,[z0,z1,z3,z7,z143,z5,z452]),(0,[z0,z1,z2,z3,z7,z5,z453]),(0,[z0,z1,z2,z3,z7,z454,z5])]],
   [[(0,[z0,z1,z2,z3,z7,z187,z143]),(0,[z0,z455,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z456,z7,z5]),(0,[z0,z44,z119,z1,z3,z7,z5])],[(0,[z0,z457,z1,z2,z3,z7,z5]),(0,[z0,z458,z1,z2,z3,z7,z5]),(0,[z0,z1,z459,z2,z3,z7,z5])],[(0,[z0,z1,z2,z460,z3,z7,z5]),(0,[z0,z461,z1,z2,z3,z7,z5]),(0,[z0,z44,z248,z2,z3,z7,z5])],[(1,[z0,z1,z2,z3,z15,z5]),(0,[z0,z1,z2,z3,z7,z281,z5]),(0,[z462,z0,z1,z2,z3,z7,z5])],[(0,[z0,z1,z2,z3,z463,z7,z5]),(0,[z0,z1,z2,z3,z464,z7,z5]),(0,[z0,z433,z1,z2,z3,z7,z5])],[(1,[z0,z1,z2,z3,z203,z5]),(0,[z0,z465,z1,z2,z3,z7,z5]),(0,[z0,z466,z1,z2,z3,z7,z5]),(0,[z0,z467,z1,z2,z3,z7,z5])],[(0,[z0,z1,z75,z2,z3,z58,z5]),(0,[z0,z114,z1,z238,z3,z7,z5]),(0,[z0,z114,z1,z108,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z187,z5])],[(0,[z98,z0,z35,z2,z3,z7,z5]),(0,[z0,z468,z1,z2,z3,z7,z5])]],
   [[(0,[z0,z1,z2,z3,z7,z469,z5]),(0,[z0,z1,z2,z3,z16,z104,z5]),(0,[z0,z1,z470,z2,z3,z7,z5]),(0,[z0,z87,z1,z2,z3,z7,z5]),(1,[z0,z195,z1,z2,z7,z5])],[(0,[z0,z1,z2,z3,z471,z7,z5]),(0,[z0,z472,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z473,z7,z5]),(0,[z0,z19,z1,z2,z108,z7,z5]),(0,[z0,z1,z2,z3,z474,z7,z5]),(0,[z0,z475,z1,z2,z3,z7,z5]),(0,[z0,z18,z133,z1,z2,z3,z7])],[(0,[z98,z74,z1,z2,z3,z7,z5]),(0,[z98,z1,z75,z2,z3,z7,z5]),(1,[z0,z1,z3,z7,z5,z452]),(0,[z0,z1,z2,z108,z3,z7,z5]),(0,[z0,z1,z2,z476,z3,z7,z5])],[(0,[z98,z0,z1,z107,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z477,z5]),(1,[z0,z1,z2,z3,z478,z5]),(0,[z166,z0,z19,z1,z3,z7,z5]),(0,[z0,z1,z2,z388,z3,z7,z5]),(0,[z0,z479,z1,z2,z3,z7,z5]),(0,[z0,z1,z480,z2,z3,z7,z5])],[(0,[z0,z481,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z16,z5,z27]),(0,[z0,z1,z2,z22,z3,z58,z5]),(0,[z0,z80,z2,z81,z3,z7,z5]),(1,[z0,z1,z2,z13,z111,z5])],[(0,[z0,z2,z3,z7,z187,z5,z138]),(0,[z0,z1,z2,z3,z7,z482,z5])],[(0,[z0,z1,z2,z3,z7,z5,z483]),(0,[z0,z484,z1,z2,z3,z7,z5]),(0,[z485,z0,z1,z2,z3,z7,z5]),(0,[z0,z486,z1,z2,z3,z7,z5]),(0,[z0,z487,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z488,z5]),(1,[z0,z119,z1,z3,z7,z45]),(0,[z0,z1,z2,z3,z489,z7,z5])],[(0,[z0,z1,z2,z490,z3,z7,z5])]],
   [[(0,[z0,z491,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z7,z5]),(0,[z267,z0,z1,z2,z3,z16,z5]),(0,[z0,z18,z1,z2,z3,z7,z143]),(0,[z0,z2,z81,z3,z7,z187,z5]),(0,[z0,z1,z2,z3,z7,z5,z492]),(0,[z0,z1,z2,z3,z493,z7,z5]),(0,[z0,z119,z1,z2,z3,z7,z181]),(1,[z0,z433,z1,z2,z3,z7])],[(0,[z74,z222,z1,z2,z3,z7,z5]),(1,[z0,z200,z1,z3,z16,z5]),(0,[z0,z1,z2,z494,z3,z7,z5]),(0,[z0,z48,z21,z2,z3,z7,z5]),(0,[z0,z44,z1,z2,z3,z7,z5])],[(0,[z0,z1,z2,z3,z407,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z495]),(0,[z0,z361,z1,z2,z3,z7,z5]),(0,[z0,z248,z1,z2,z3,z7,z5])],[(0,[z0,z1,z2,z3,z409,z7,z5]),(0,[z0,z206,z1,z2,z3,z58,z5]),(0,[z0,z31,z1,z81,z3,z7,z5]),(0,[z0,z206,z1,z2,z3,z7,z138])],[(0,[z70,z0,z1,z2,z3,z16,z5]),(0,[z0,z1,z2,z496,z3,z7,z5]),(0,[z497,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z498,z5])],[(0,[z499,z0,z1,z2,z3,z7,z5]),(0,[z0,z21,z1,z2,z3,z16,z5]),(0,[z0,z500,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z333,z7,z5]),(0,[z0,z35,z2,z81,z3,z7,z5]),(0,[z0,z1,z2,z501,z3,z7,z5]),(1,[z0,z1,z2,z3,z5,z403]),(0,[z0,z1,z2,z3,z502,z7,z5])],[(0,[z0,z1,z2,z13,z3,z17,z5]),(0,[z0,z18,z1,z2,z3,z7,z5])],[(1,[z0,z1,z2,z3,z7,z332]),(0,[z0,z1,z2,z3,z16,z91,z5]),(0,[z0,z1,z2,z3,z7,z503,z5])]],
   [[(1,[z0,z1,z2,z3,z471,z5]),(0,[z0,z1,z504,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z58,z88,z5]),(0,[z0,z1,z2,z53,z3,z7,z5]),(0,[z0,z133,z1,z2,z3,z5,z27])],[(0,[z0,z1,z2,z3,z505,z7,z5]),(0,[z0,z506,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z507,z5]),(0,[z0,z508,z1,z2,z3,z7,z5]),(1,[z0,z287,z1,z2,z3,z5])],[(0,[z509,z0,z1,z2,z3,z7,z5]),(0,[z98,z0,z2,z3,z7,z187,z5]),(0,[z0,z1,z2,z3,z510,z7,z5]),(0,[z29,z0,z1,z2,z3,z58,z5]),(0,[z511,z0,z1,z2,z3,z7,z5])],[(0,[z0,z1,z2,z3,z512,z7,z5]),(0,[z0,z513,z1,z2,z3,z7,z5])],[(0,[z0,z1,z2,z41,z8,z7,z5]),(0,[z0,z1,z2,z3,z58,z514,z5]),(0,[z0,z515,z1,z2,z3,z7,z5])],[(0,[z74,z0,z1,z2,z3,z471,z5]),(0,[z0,z31,z1,z2,z3,z58,z5]),(0,[z120,z0,z1,z2,z3,z7,z143]),(0,[z0,z1,z516,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z517]),(0,[z0,z1,z2,z3,z7,z5,z518]),(0,[z0,z1,z2,z3,z7,z519,z5])],[(0,[z38,z0,z1,z2,z520,z7,z5]),(0,[z0,z1,z2,z3,z16,z16,z5]),(0,[z0,z1,z2,z3,z7,z521,z5]),(1,[z0,z1,z2,z3,z24,z5])],[(0,[z38,z0,z1,z39,z3,z7,z5]),(0,[z0,z1,z2,z63,z3,z16,z5]),(0,[z0,z50,z1,z2,z3,z16,z5]),(0,[z0,z1,z2,z522,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z523])]],
   [[(0,[z0,z1,z2,z39,z3,z7,z5]),(0,[z0,z1,z2,z3,z16,z5,z131]),(0,[z0,z1,z2,z3,z524,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z525]),(0,[z0,z1,z2,z526,z3,z7,z5])],[(0,[z527,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z58,z5,z528]),(1,[z0,z1,z2,z10,z7,z5]),(0,[z0,z1,z2,z3,z7,z529,z5]),(0,[z530,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z531,z3,z7,z5])],[(1,[z0,z1,z2,z520,z7,z5]),(0,[z0,z1,z2,z3,z532,z7,z5]),(0,[z0,z103,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z533,z5])],[(0,[z120,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z326,z5]),(0,[z0,z534,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z535,z7,z5]),(0,[z0,z1,z536,z2,z3,z7,z5])],[(0,[z0,z537,z1,z2,z3,z58,z5]),(0,[z0,z1,z2,z3,z58,z104,z5]),(0,[z0,z538,z1,z2,z3,z7,z5]),(0,[z0,z287,z1,z2,z3,z5,z45])],[(0,[z166,z0,z1,z2,z3,z58,z5]),(1,[z0,z1,z3,z193,z7,z5]),(0,[z0,z44,z1,z81,z3,z7,z5]),(0,[z0,z539,z1,z2,z3,z7,z5]),(0,[z0,z540,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z541,z3,z7,z5])],[(0,[z542,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z543]),(0,[z0,z87,z1,z2,z3,z58,z5]),(0,[z544,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z545,z7,z5]),(0,[z546,z0,z1,z2,z3,z7,z5]),(0,[z547,z0,z1,z2,z3,z7,z5])],[(0,[z548,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z549,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z550]),(0,[z0,z1,z2,z3,z7,z5,z551])]],
   [[(0,[z0,z222,z1,z2,z3,z16,z5]),(0,[z0,z1,z2,z552,z3,z7,z5]),(0,[z0,z1,z2,z553,z3,z7,z5]),(0,[z0,z1,z2,z3,z58,z5,z27]),(0,[z0,z1,z2,z3,z7,z554,z5]),(0,[z0,z12,z2,z3,z51,z7,z5]),(0,[z0,z1,z2,z555,z3,z7,z5])],[(0,[z98,z0,z222,z2,z3,z7,z5]),(0,[z0,z556,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z557]),(0,[z0,z1,z2,z3,z210,z7,z5]),(0,[z0,z1,z558,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z559,z7,z5])],[(0,[z0,z1,z2,z3,z7,z560,z5]),(0,[z0,z133,z1,z2,z3,z16,z5]),(0,[z0,z216,z1,z2,z3,z7,z5]),(0,[z0,z481,z1,z2,z3,z58,z5]),(1,[z0,z1,z2,z3,z126,z7]),(0,[z0,z35,z1,z2,z3,z7,z187]),(0,[z0,z561,z1,z2,z3,z7,z5])],[(1,[z0,z1,z338,z3,z7,z5]),(0,[z0,z1,z75,z2,z3,z7,z5]),(0,[z0,z562,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z563,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z564]),(0,[z0,z565,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z566,z7,z5])],[(0,[z0,z567,z1,z2,z3,z7,z5]),(0,[z38,z0,z1,z2,z3,z16,z5]),(0,[z0,z1,z112,z2,z3,z58,z5]),(0,[z568,z0,z1,z2,z3,z7,z5])],[(0,[z0,z1,z1,z2,z3,z7,z5]),(0,[z0,z569,z1,z2,z3,z7,z5]),(0,[z570,z0,z1,z2,z3,z7,z5]),(0,[z571,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z572,z5]),(0,[z0,z2,z22,z3,z49,z7,z5]),(0,[z0,z573,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z7,z5,z197,z45]),(0,[z0,z1,z2,z3,z24,z5,z45]),(0,[z0,z18,z1,z156,z3,z7,z5]),(1,[z0,z1,z2,z3,z177,z17])],[(0,[z0,z1,z2,z3,z574,z7,z5]),(0,[z0,z1,z2,z575,z3,z7,z5]),(1,[z146,z1,z2,z3,z58,z5]),(0,[z0,z119,z1,z2,z3,z58,z5]),(0,[z0,z1,z576,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z577])],[(0,[z0,z1,z2,z3,z245,z7,z5]),(0,[z0,z1,z2,z3,z7,z121,z5]),(0,[z0,z1,z2,z3,z7,z578,z5])]],
   [[(0,[z0,z579,z1,z2,z3,z7,z5]),(0,[z0,z221,z1,z2,z3,z16,z5]),(0,[z0,z1,z2,z3,z16,z181,z5]),(1,[z0,z1,z273,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z580])],[(0,[z0,z581,z1,z2,z3,z7,z5]),(0,[z0,z19,z1,z2,z3,z16,z5]),(0,[z0,z582,z1,z2,z3,z7,z5])],[(0,[z583,z0,z1,z2,z3,z7,z5])],[(0,[z0,z1,z2,z3,z99,z7,z5]),(1,[z0,z1,z2,z3,z7,z93]),(0,[z0,z500,z1,z2,z3,z58,z5]),(0,[z0,z1,z2,z3,z58,z91,z5]),(0,[z0,z114,z1,z3,z7,z5,z45]),(0,[z0,z584,z1,z2,z3,z7,z5]),(0,[z0,z585,z1,z2,z3,z7,z5]),(0,[z0,z35,z1,z2,z3,z7,z5]),(0,[z0,z35,z1,z2,z3,z7,z181]),(0,[z0,z1,z2,z3,z586,z7,z5]),(0,[z0,z1,z2,z3,z7,z64,z5])],[(0,[z77,z0,z1,z2,z3,z109,z5]),(0,[z0,z1,z2,z78,z49,z7,z5]),(0,[z0,z587,z1,z2,z3,z7,z5]),(0,[z0,z18,z1,z2,z3,z58,z5]),(0,[z0,z588,z1,z2,z3,z7,z5]),(0,[z0,z152,z1,z2,z3,z49,z7]),(0,[z0,z1,z2,z589,z3,z7,z5])],[(0,[z0,z1,z238,z2,z3,z16,z5]),(1,[z0,z48,z2,z49,z7,z5]),(0,[z0,z1,z2,z3,z590,z7,z5]),(0,[z0,z591,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z592,z5])],[(0,[z38,z0,z1,z3,z7,z5,z45]),(0,[z593,z0,z1,z2,z3,z7,z5]),(0,[z0,z12,z1,z273,z3,z7,z5]),(0,[z0,z1,z2,z594,z3,z7,z5])],[(0,[z77,z0,z1,z2,z3,z16,z5]),(0,[z0,z1,z2,z3,z7,z5,z45])]],
   [[(0,[z595,z0,z1,z2,z3,z7,z5]),(0,[z596,z0,z1,z2,z3,z7,z5]),(0,[z597,z0,z1,z2,z3,z7,z5]),(0,[z598,z0,z1,z2,z3,z7,z5]),(0,[z599,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z17,z5,z27]),(0,[z0,z600,z1,z2,z3,z7,z5])],[(0,[z0,z1,z2,z3,z7,z5,z601]),(0,[z0,z602,z1,z2,z3,z7,z5]),(0,[z0,z19,z1,z2,z8,z7,z5])],[(0,[z0,z1,z2,z290,z3,z7,z5]),(0,[z77,z0,z1,z2,z41,z7,z5]),(0,[z77,z0,z1,z2,z3,z7,z93]),(0,[z0,z1,z2,z3,z58,z16,z5]),(0,[z0,z200,z1,z2,z3,z16,z5]),(0,[z0,z1,z2,z3,z111,z58,z5]),(0,[z0,z1,z2,z3,z7,z5,z164]),(0,[z0,z1,z2,z3,z7,z143,z45]),(1,[z0,z436,z1,z3,z7,z5]),(1,[z0,z361,z1,z3,z7,z5]),(0,[z0,z35,z2,z3,z7,z5,z138])],[(0,[z0,z1,z2,z3,z7,z603,z5]),(0,[z604,z0,z1,z2,z3,z7,z5])],[(0,[z605,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z606,z3,z7,z5]),(0,[z0,z1,z2,z108,z3,z16,z5]),(0,[z0,z1,z2,z3,z58,z5,z131]),(0,[z0,z48,z2,z3,z49,z7,z5]),(0,[z0,z1,z2,z3,z7,z607,z5])],[(0,[z0,z1,z2,z3,z608,z7,z5]),(1,[z0,z1,z2,z3,z300,z5]),(0,[z0,z1,z2,z3,z126,z7,z5])],[(0,[z0,z1,z2,z39,z3,z58,z5]),(0,[z0,z609,z1,z2,z3,z7,z5])],[(0,[z98,z0,z75,z2,z3,z7,z5]),(0,[z0,z610,z1,z2,z3,z7,z5]),(0,[z29,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z611,z2,z3,z7,z5]),(0,[z0,z612,z1,z2,z3,z7,z5]),(0,[z613,z0,z1,z2,z3,z7,z5]),(0,[z0,z614,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z615])]],
   [[(0,[z0,z277,z1,z2,z3,z7,z5]),(0,[z0,z1,z142,z2,z3,z7,z5]),(0,[z0,z103,z1,z2,z3,z58,z5]),(0,[z0,z1,z2,z3,z7,z616,z5]),(0,[z0,z50,z1,z2,z3,z88,z5]),(0,[z0,z617,z1,z2,z3,z7,z5]),(0,[z618,z0,z1,z2,z3,z7,z5])],[(0,[z98,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z81,z3,z16,z5]),(0,[z120,z0,z1,z2,z3,z58,z5]),(0,[z0,z619,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z620,z7,z5])],[(1,[z0,z1,z107,z3,z7,z5]),(0,[z29,z0,z1,z2,z3,z76,z5]),(0,[z0,z436,z21,z1,z3,z7,z5]),(0,[z621,z0,z1,z2,z3,z7,z5]),(0,[z0,z31,z1,z2,z3,z7,z5])],[(0,[z622,z0,z1,z2,z3,z7,z5]),(0,[z0,z623,z1,z2,z3,z7,z5]),(0,[z0,z624,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z111,z7,z91,z5])],[(1,[z0,z263,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z625,z7,z5]),(1,[z0,z9,z1,z2,z7,z5]),(0,[z0,z1,z2,z3,z7,z626,z5]),(0,[z0,z1,z2,z3,z627,z7,z5])],[(0,[z267,z0,z1,z2,z3,z7,z164]),(0,[z0,z1,z628,z2,z3,z7,z5])],[(0,[z0,z1,z2,z78,z3,z7,z5]),(0,[z0,z629,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z630,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z631]),(0,[z0,z632,z1,z2,z3,z7,z5])],[(0,[z633,z0,z1,z2,z3,z7,z5]),(1,[z0,z1,z2,z3,z7,z115])]],
   [[(0,[z0,z1,z2,z634,z3,z7,z5]),(0,[z29,z1,z2,z3,z41,z7,z5]),(0,[z0,z80,z1,z2,z3,z58,z5]),(0,[z0,z1,z81,z3,z7,z5,z45]),(0,[z635,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z636]),(0,[z0,z1,z2,z3,z637,z7,z5]),(0,[z0,z87,z1,z2,z7,z64,z5])],[(0,[z0,z1,z2,z3,z7,z5,z638]),(0,[z0,z537,z1,z2,z3,z7,z5]),(0,[z0,z639,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z640,z5])],[(0,[z166,z0,z1,z2,z3,z7,z5]),(0,[z38,z0,z1,z2,z3,z478,z5]),(0,[z146,z42,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z452]),(0,[z0,z12,z1,z2,z3,z51,z5]),(1,[z0,z218,z2,z3,z7,z5])],[(0,[z0,z1,z2,z3,z7,z382,z5]),(0,[z38,z0,z31,z1,z3,z7,z5]),(0,[z641,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z164,z138]),(0,[z0,z642,z1,z2,z3,z7,z5])],[(0,[z0,z1,z2,z3,z7,z5,z643]),(0,[z0,z1,z2,z3,z51,z16,z5]),(0,[z0,z1,z2,z3,z58,z181,z5]),(0,[z0,z1,z2,z3,z7,z5,z644]),(0,[z0,z1,z2,z3,z645,z7,z5])],[(0,[z0,z646,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z13,z3,z7,z5]),(0,[z0,z87,z1,z2,z3,z111,z5]),(0,[z647,z0,z1,z2,z3,z7,z5])],[(0,[z0,z1,z2,z3,z7,z181,z143]),(0,[z0,z1,z112,z2,z7,z64,z5])],[(0,[z0,z1,z648,z2,z3,z7,z5]),(0,[z0,z649,z1,z2,z3,z7,z5]),(0,[z0,z359,z1,z2,z3,z16,z5]),(0,[z0,z200,z1,z3,z7,z16,z5]),(0,[z0,z1,z2,z650,z3,z7,z5]),(0,[z0,z651,z1,z2,z3,z7,z5])]],
   [[(0,[z652,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z653,z2,z3,z7,z5]),(1,[z1,z2,z3,z58,z16,z5]),(0,[z654,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z655,z2,z3,z7,z5]),(0,[z120,z0,z1,z2,z230,z7,z5]),(0,[z0,z50,z12,z2,z3,z7,z5]),(0,[z656,z0,z1,z2,z3,z7,z5])],[(0,[z0,z35,z1,z2,z3,z58,z5]),(0,[z0,z657,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z658,z5]),(0,[z0,z1,z112,z2,z3,z7,z5]),(0,[z0,z1,z659,z2,z3,z7,z5])],[(0,[z0,z222,z2,z81,z3,z7,z5]),(0,[z0,z56,z1,z2,z3,z58,z5]),(0,[z0,z1,z2,z3,z7,z660,z5]),(0,[z0,z661,z1,z2,z3,z7,z5]),(0,[z0,z662,z1,z2,z3,z7,z5]),(0,[z0,z31,z103,z1,z3,z7,z5]),(0,[z0,z1,z2,z3,z663,z7,z5])],[(0,[z0,z1,z2,z664,z3,z7,z5]),(0,[z0,z119,z1,z2,z3,z7,z5])],[(0,[z0,z1,z2,z63,z3,z7,z164]),(0,[z0,z665,z1,z2,z3,z7,z5]),(0,[z0,z103,z1,z2,z3,z37,z5]),(0,[z666,z0,z1,z2,z3,z7,z5])],[(0,[z222,z1,z75,z2,z3,z7,z5]),(0,[z0,z133,z1,z2,z3,z7,z27])],[(0,[z0,z1,z2,z667,z3,z7,z5]),(0,[z77,z0,z1,z2,z78,z7,z5]),(0,[z0,z1,z2,z3,z49,z16,z5]),(0,[z0,z668,z1,z2,z3,z7,z5]),(0,[z0,z18,z1,z2,z3,z177,z7])],[(0,[z0,z1,z669,z2,z3,z7,z5]),(0,[z0,z18,z35,z1,z2,z3,z7])]],
   [[],[(0,[z670,z0,z1,z2,z3,z7,z5]),(0,[z166,z0,z1,z238,z3,z7,z5]),(0,[z166,z0,z1,z108,z3,z7,z5]),(0,[z0,z1,z2,z3,z89,z58,z5]),(0,[z0,z671,z1,z2,z3,z7,z5]),(0,[z0,z206,z1,z2,z3,z7,z45])],[(0,[z672,z0,z1,z2,z3,z7,z5]),(0,[z673,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z520,z7,z5]),(0,[z0,z1,z2,z3,z674,z7,z5])],[(0,[z0,z48,z1,z2,z22,z7,z5]),(0,[z0,z1,z112,z2,z108,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z675])],[(0,[z0,z1,z2,z3,z7,z5,z676]),(1,[z0,z426,z1,z2,z3,z5])],[(0,[z0,z565,z1,z2,z3,z16,z5]),(0,[z0,z677,z1,z2,z3,z7,z5])],[(0,[z0,z1,z2,z160,z3,z7,z5]),(0,[z0,z1,z678,z2,z3,z7,z5]),(0,[z0,z1,z2,z63,z3,z7,z131])],[(0,[z98,z0,z1,z2,z3,z58,z5]),(0,[z0,z114,z1,z39,z3,z7,z5]),(0,[z0,z1,z2,z3,z16,z113,z5]),(0,[z0,z2,z3,z7,z178,z5,z164]),(0,[z0,z1,z2,z3,z111,z7,z5])]],
   [[(1,[z0,z1,z2,z3,z237,z5]),(0,[z0,z1,z2,z3,z679,z7,z5]),(0,[z0,z1,z112,z108,z3,z7,z5])],[(1,[z0,z1,z2,z3,z245,z5])],[(0,[z0,z0,z1,z2,z3,z7,z5]),(0,[z0,z680,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z681,z7,z5])],[(0,[z682,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z478,z7,z5]),(0,[z0,z1,z2,z683,z3,z7,z5]),(0,[z0,z1,z2,z22,z3,z16,z5]),(0,[z0,z1,z2,z3,z7,z88,z5]),(0,[z0,z684,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z685,z7,z5]),(1,[z0,z1,z2,z7,z5,z197])],[(0,[z0,z1,z2,z78,z3,z58,z5]),(0,[z0,z1,z2,z3,z410,z16,z5]),(0,[z686,z0,z1,z2,z3,z7,z5]),(0,[z0,z687,z1,z2,z3,z7,z5]),(0,[z0,z133,z1,z2,z3,z7,z17])],[(0,[z74,z0,z222,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z193,z7,z5]),(0,[z0,z133,z1,z2,z13,z3,z5]),(0,[z0,z1,z2,z3,z7,z5,z688])],[(0,[z0,z1,z2,z3,z7,z5,z689]),(0,[z0,z1,z2,z3,z7,z5,z690])],[(0,[z146,z0,z1,z2,z3,z58,z5]),(0,[z0,z1,z2,z3,z7,z514,z5]),(1,[z0,z1,z2,z3,z7,z94])]],
   [[],[],[(0,[z0,z1,z2,z691,z3,z7,z5]),(0,[z0,z206,z1,z2,z3,z16,z5]),(0,[z0,z1,z2,z3,z177,z16,z5]),(0,[z0,z692,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z5,z403])],[(0,[z29,z77,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z41,z7,z5]),(0,[z0,z1,z2,z3,z424,z16,z5]),(0,[z0,z1,z693,z2,z3,z7,z5]),(0,[z0,z1,z2,z13,z3,z58,z5]),(0,[z0,z1,z2,z3,z7,z694,z5]),(0,[z0,z695,z1,z2,z3,z7,z5])],[(0,[z696,z0,z1,z2,z3,z7,z5]),(0,[z38,z0,z1,z2,z3,z4,z5]),(0,[z38,z0,z1,z3,z37,z7,z5]),(0,[z38,z0,z44,z1,z3,z7,z5]),(0,[z0,z1,z697,z2,z3,z7,z5]),(0,[z0,z114,z1,z2,z3,z16,z5]),(0,[z0,z1,z2,z3,z7,z5,z528]),(0,[z0,z698,z1,z2,z3,z7,z5])],[(0,[z0,z80,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z37,z7,z5]),(0,[z0,z1,z2,z3,z699,z7,z5]),(0,[z0,z700,z1,z2,z3,z7,z5]),(0,[z0,z87,z18,z1,z2,z7,z5]),(0,[z0,z426,z1,z2,z3,z5,z131])],[(0,[z701,z0,z1,z2,z3,z7,z5]),(0,[z0,z702,z1,z2,z3,z7,z5]),(1,[z267,z1,z2,z3,z7,z164]),(0,[z0,z1,z2,z3,z7,z703,z5]),(0,[z0,z1,z2,z3,z7,z704,z5])],[(0,[z1,z238,z2,z39,z3,z7,z5]),(0,[z0,z1,z2,z3,z16,z143,z5]),(0,[z0,z19,z114,z1,z3,z7,z5]),(0,[z705,z0,z1,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z104,z5]),(0,[z0,z1,z706,z2,z3,z7,z5])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z707,z1,z2,z3,z5]),(0,[z267,z1,z2,z3,z58,z164]),(0,[z0,z1,z2,z3,z177,z59]),(0,[z0,z1,z2,z3,z7,z140]),(0,[z0,z708,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z709,z5]),(0,[z0,z1,z2,z3,z710,z5]),(0,[z0,z133,z200,z1,z3,z5]),(0,[z0,z152,z1,z2,z3,z7]),(0,[z0,z1,z2,z3,z7,z711]),(0,[z0,z9,z35,z1,z2,z7]),(0,[z0,z433,z1,z2,z13,z3])],[(0,[z0,z386,z81,z3,z7,z5]),(0,[z38,z1,z39,z149,z7,z5]),(0,[z166,z1,z238,z3,z151,z5]),(0,[z0,z200,z1,z3,z193,z5]),(0,[z0,z216,z1,z2,z3,z27]),(0,[z0,z481,z1,z3,z258,z5]),(0,[z0,z35,z2,z3,z7,z205])],[(0,[z0,z1,z2,z3,z712,z5]),(0,[z0,z1,z2,z3,z210,z17]),(0,[z0,z9,z287,z1,z2,z5])],[(0,[z38,z169,z39,z3,z7,z5]),(0,[z0,z2,z3,z7,z713,z5]),(0,[z1,z238,z714,z3,z7,z5]),(0,[z0,z359,z1,z2,z91,z5]),(0,[z1,z2,z3,z7,z143,z715]),(0,[z0,z716,z1,z2,z3,z7])],[(0,[z0,z1,z2,z149,z7,z5]),(0,[z0,z717,z2,z3,z7,z5]),(0,[z0,z71,z1,z3,z7,z5]),(0,[z0,z718,z81,z3,z7,z5]),(0,[z1,z2,z3,z7,z5,z719]),(0,[z0,z1,z2,z7,z5,z720]),(0,[z0,z2,z3,z7,z711,z5]),(0,[z0,z9,z1,z112,z7,z5]),(0,[z0,z44,z218,z3,z7,z181]),(0,[z0,z44,z1,z3,z7,z721]),(0,[z0,z18,z1,z2,z7,z131])],[(0,[z0,z1,z2,z290,z7,z332])],[(0,[z38,z1,z39,z3,z58,z5]),(0,[z0,z1,z53,z41,z7,z5]),(0,[z1,z2,z3,z58,z16,z5]),(0,[z0,z1,z2,z3,z722,z5])]],
   [[(0,[z0,z1,z107,z3,z7,z168]),(0,[z0,z200,z1,z3,z4,z5]),(0,[z25,z1,z2,z3,z58,z5]),(0,[z0,z1,z2,z3,z723,z5]),(0,[z0,z1,z2,z3,z7,z724]),(0,[z0,z1,z2,z3,z725,z5]),(0,[z0,z1,z2,z3,z17,z381]),(0,[z0,z287,z119,z1,z3,z45])],[(0,[z0,z726,z1,z2,z3,z16])],[(0,[z0,z1,z2,z3,z58,z5]),(0,[z98,z75,z107,z3,z7,z5]),(0,[z0,z263,z2,z3,z7,z168]),(0,[z0,z1,z2,z3,z727,z5]),(0,[z0,z1,z2,z10,z16,z5]),(0,[z1,z2,z3,z681,z58,z5]),(0,[z0,z1,z2,z3,z728,z5]),(0,[z0,z35,z2,z3,z7,z711])],[(0,[z0,z1,z2,z520,z16,z5]),(0,[z0,z729,z2,z3,z7,z5]),(0,[z0,z1,z180,z3,z7,z5]),(0,[z0,z1,z2,z3,z730,z5])],[(0,[z0,z1,z2,z3,z16,z731]),(0,[z0,z202,z81,z3,z7,z5]),(0,[z0,z221,z361,z3,z7,z5]),(0,[z0,z65,z1,z2,z3,z126]),(0,[z0,z18,z1,z156,z7,z131])],[(0,[z0,z1,z2,z3,z732,z5]),(0,[z77,z1,z2,z78,z58,z5]),(0,[z0,z80,z81,z3,z58,z5])],[(0,[z0,z1,z2,z99,z7,z332]),(0,[z0,z1,z2,z3,z733,z5]),(0,[z0,z142,z238,z3,z7,z5]),(0,[z0,z1,z2,z3,z4,z208]),(0,[z0,z1,z2,z734,z7,z5]),(0,[z0,z1,z3,z193,z16,z5]),(0,[z0,z2,z3,z730,z88,z5]),(0,[z0,z1,z2,z3,z735,z5])],[(0,[z1,z2,z3,z736,z7,z5]),(0,[z42,z1,z3,z193,z16,z5])]],
   [[(0,[z0,z1,z2,z3,z737,z5])],[(0,[z0,z738,z1,z3,z237,z5]),(0,[z0,z427,z2,z22,z7,z5]),(0,[z0,z1,z739,z3,z16,z5]),(0,[z374,z1,z2,z3,z58,z5]),(0,[z740,z1,z2,z3,z7,z5]),(0,[z0,z206,z1,z53,z3,z7])],[(0,[z74,z222,z2,z3,z16,z5]),(0,[z0,z1,z2,z3,z7,z741]),(0,[z0,z1,z2,z3,z742,z5])],[(0,[z0,z1,z2,z3,z7,z743]),(0,[z0,z1,z3,z744,z237,z5]),(0,[z38,z1,z39,z3,z7,z208]),(0,[z1,z714,z39,z3,z7,z5]),(0,[z0,z221,z114,z3,z16,z5]),(0,[z0,z174,z2,z3,z409,z5]),(0,[z0,z87,z1,z2,z679,z5]),(0,[z0,z35,z2,z3,z7,z138]),(0,[z0,z1,z3,z745,z104,z5])],[(0,[z0,z1,z338,z3,z16,z5]),(0,[z0,z1,z2,z3,z746,z5])],[(0,[z700,z1,z2,z3,z58,z5]),(0,[z0,z747,z1,z2,z3,z7]),(0,[z0,z1,z2,z3,z748,z5])],[(0,[z0,z1,z2,z3,z7,z208]),(0,[z0,z1,z132,z3,z7,z5]),(0,[z0,z1,z2,z3,z749,z5]),(0,[z0,z44,z1,z3,z16,z181]),(0,[z0,z12,z273,z3,z51,z5])],[(0,[z0,z1,z2,z3,z237,z5]),(0,[z29,z1,z2,z41,z76,z5]),(0,[z0,z1,z3,z16,z5,z452]),(0,[z0,z1,z2,z3,z5,z750]),(0,[z497,z1,z2,z3,z58,z5]),(0,[z0,z1,z2,z3,z751,z7]),(0,[z0,z752,z1,z2,z3,z7])]],
   [[(0,[z0,z142,z2,z149,z7,z5]),(0,[z0,z1,z3,z7,z745,z5])],[(0,[z0,z1,z2,z3,z753,z5]),(0,[z0,z1,z2,z230,z7,z5]),(0,[z0,z1,z3,z7,z5,z754]),(0,[z0,z1,z2,z3,z109,z93]),(0,[z0,z1,z2,z3,z210,z113]),(0,[z0,z263,z2,z3,z7,z138]),(0,[z0,z1,z2,z3,z755,z5])],[(0,[z0,z1,z338,z290,z7,z5]),(0,[z127,z1,z2,z41,z7,z5]),(0,[z0,z48,z65,z2,z49,z5]),(1,[z0,z2,z3,z730,z5]),(0,[z0,z87,z433,z1,z2,z91]),(1,[z0,z1,z2,z7,z756]),(0,[z0,z1,z2,z63,z7,z756])],[(0,[z0,z1,z2,z757,z7,z5]),(0,[z0,z1,z758,z3,z7,z5]),(0,[z98,z75,z2,z3,z58,z5]),(0,[z23,z1,z2,z3,z58,z5]),(0,[z14,z1,z2,z3,z7,z164]),(0,[z759,z1,z2,z3,z7,z5])],[(0,[z0,z1,z2,z3,z16,z93]),(0,[z0,z1,z2,z7,z5,z760]),(0,[z0,z263,z2,z3,z7,z45]),(0,[z0,z1,z2,z3,z126,z305]),(0,[z0,z87,z433,z1,z2,z7])],[(0,[z0,z1,z338,z3,z134,z5]),(0,[z0,z142,z2,z3,z58,z5]),(0,[z0,z761,z1,z3,z7,z5]),(0,[z0,z1,z762,z3,z7,z5]),(0,[z0,z18,z1,z2,z7,z676]),(1,[z0,z87,z433,z1,z2])],[(0,[z0,z1,z2,z763,z7,z5]),(0,[z0,z48,z2,z49,z16,z5]),(0,[z0,z1,z2,z3,z58,z140]),(0,[z0,z1,z2,z764,z7,z5])],[(0,[z267,z1,z2,z3,z7,z715]),(0,[z599,z1,z2,z3,z7,z143]),(0,[z0,z1,z2,z3,z765,z7])]],
   [[(0,[z0,z169,z2,z149,z7,z5]),(0,[z0,z247,z1,z3,z7,z5]),(0,[z0,z247,z1,z3,z7,z181]),(0,[z0,z248,z2,z3,z7,z5]),(0,[z0,z114,z662,z3,z7,z5]),(0,[z0,z1,z2,z3,z5,z766]),(0,[z0,z767,z1,z2,z3,z5]),(0,[z0,z768,z1,z2,z3,z5]),(0,[z0,z1,z3,z7,z721,z45]),(0,[z0,z248,z2,z3,z7,z181])],[(0,[z0,z1,z2,z769,z7,z5]),(0,[z0,z1,z156,z3,z58,z5])],[(0,[z0,z1,z338,z99,z7,z5]),(0,[z212,z1,z39,z3,z7,z5]),(0,[z0,z9,z1,z81,z7,z5]),(0,[z0,z31,z1,z3,z104,z5])],[(0,[z0,z1,z2,z149,z58,z5]),(0,[z0,z1,z2,z3,z770,z5]),(0,[z0,z1,z53,z78,z7,z5]),(0,[z0,z436,z1,z3,z16,z5]),(0,[z0,z361,z1,z3,z16,z5]),(0,[z0,z1,z771,z3,z16,z5]),(0,[z621,z1,z2,z3,z16,z5]),(0,[z0,z18,z1,z2,z58,z131]),(0,[z0,z71,z1,z3,z58,z5]),(0,[z511,z1,z2,z3,z58,z5]),(0,[z0,z1,z2,z3,z7,z772]),(0,[z0,z1,z2,z3,z773,z5]),(0,[z0,z2,z3,z7,z711,z138]),(0,[z0,z1,z2,z3,z774,z5]),(0,[z0,z1,z2,z3,z775,z27]),(1,[z0,z195,z133,z1,z2])],[(0,[z0,z1,z2,z3,z776,z5]),(0,[z0,z1,z2,z3,z777,z5]),(0,[z0,z1,z2,z3,z778,z5]),(0,[z0,z1,z2,z3,z779,z5]),(0,[z0,z780,z1,z3,z7,z5])],[(0,[z0,z169,z2,z3,z58,z5]),(0,[z0,z781,z1,z3,z58,z5]),(0,[z267,z1,z2,z3,z7,z164]),(0,[z0,z87,z433,z1,z2,z5])],[(0,[z0,z18,z1,z2,z456,z7])],[(0,[z0,z1,z2,z3,z782,z5]),(0,[z396,z1,z2,z3,z16,z5]),(0,[z0,z1,z2,z3,z7,z783]),(0,[z784,z1,z2,z3,z7,z5])]],
   [[(0,[z0,z1,z2,z3,z785,z5]),(0,[z98,z786,z2,z3,z7,z5]),(0,[z613,z1,z2,z3,z16,z5]),(0,[z0,z119,z1,z3,z24,z45])],[(0,[z0,z738,z1,z3,z7,z5]),(0,[z0,z142,z2,z3,z7,z208]),(0,[z0,z1,z2,z520,z478,z5]),(0,[z0,z1,z180,z3,z58,z5]),(0,[z0,z1,z2,z3,z787,z5])],[(0,[z0,z1,z2,z788,z7,z5]),(0,[z0,z19,z1,z8,z7,z5])],[(0,[z0,z1,z3,z744,z7,z5]),(0,[z1,z2,z3,z789,z7,z5]),(0,[z0,z1,z2,z3,z126,z16]),(0,[z0,z1,z3,z16,z790,z5]),(0,[z0,z1,z112,z108,z58,z5]),(0,[z0,z1,z2,z111,z5,z219])],[(0,[z0,z1,z338,z3,z203,z5]),(0,[z0,z1,z2,z791,z7,z5]),(0,[z0,z1,z32,z108,z7,z5]),(0,[z0,z792,z1,z2,z7,z5])],[(0,[z0,z793,z1,z2,z3,z7]),(0,[z74,z2,z3,z7,z231,z5]),(0,[z0,z263,z2,z3,z16,z5]),(0,[z0,z1,z36,z3,z7,z5]),(0,[z0,z9,z114,z1,z7,z5]),(0,[z0,z794,z2,z3,z7,z5])],[(0,[z0,z795,z2,z3,z7,z5]),(0,[z0,z200,z1,z3,z58,z5]),(0,[z0,z87,z1,z2,z514,z5])],[(0,[z0,z1,z2,z3,z7,z5]),(0,[z0,z796,z1,z3,z7,z5]),(0,[z0,z1,z2,z149,z7,z208]),(0,[z212,z1,z2,z3,z16,z5]),(0,[z0,z200,z1,z3,z118,z5]),(0,[z266,z1,z2,z3,z16,z5]),(0,[z530,z1,z2,z3,z7,z143]),(0,[z0,z1,z2,z3,z797,z5])]],
   [[(0,[z0,z798,z2,z3,z7,z5]),(0,[z0,z1,z2,z7,z5,z799]),(0,[z0,z1,z2,z3,z16,z115]),(0,[z0,z1,z2,z800,z91,z5]),(0,[z0,z1,z801,z3,z7,z5])],[(0,[z0,z1,z2,z3,z802,z5]),(0,[z0,z1,z107,z290,z7,z5]),(0,[z0,z169,z2,z3,z7,z208]),(0,[z0,z803,z2,z3,z7,z5]),(0,[z0,z2,z3,z16,z178,z5]),(0,[z0,z35,z2,z3,z58,z138]),(0,[z1,z2,z3,z137,z58,z5]),(0,[z0,z1,z2,z3,z804,z5]),(0,[z0,z1,z2,z13,z800,z5]),(0,[z0,z195,z133,z1,z2,z7])],[(0,[z29,z1,z2,z41,z58,z5]),(0,[z0,z805,z2,z3,z7,z5]),(0,[z0,z80,z81,z3,z7,z5])],[(0,[z0,z1,z2,z3,z7,z806]),(0,[z0,z152,z1,z2,z78,z7]),(0,[z0,z218,z2,z3,z16,z5]),(0,[z0,z1,z2,z160,z424,z5]),(0,[z0,z1,z3,z58,z5,z452]),(0,[z0,z9,z119,z1,z7,z45]),(0,[z0,z44,z248,z3,z7,z181])],[(0,[z0,z1,z2,z3,z58,z208]),(0,[z0,z40,z1,z3,z58,z5]),(0,[z0,z1,z132,z3,z58,z5]),(0,[z0,z1,z2,z3,z807,z5]),(0,[z0,z1,z2,z808,z7,z5]),(0,[z546,z1,z2,z3,z16,z5]),(0,[z0,z248,z81,z3,z7,z5])],[(0,[z0,z1,z2,z13,z424,z5]),(0,[z0,z468,z1,z3,z7,z45])],[(0,[z0,z809,z1,z2,z3,z5]),(0,[z0,z21,z2,z810,z7,z5]),(0,[z0,z1,z2,z3,z811,z7]),(0,[z0,z1,z2,z3,z812,z5]),(0,[z0,z18,z426,z1,z2,z7])],[(0,[z0,z1,z813,z3,z7,z5]),(0,[z0,z1,z3,z7,z5,z814]),(0,[z0,z1,z2,z815,z7,z5]),(0,[z1,z2,z736,z41,z7,z5]),(0,[z285,z1,z2,z41,z7,z5]),(0,[z0,z1,z2,z230,z58,z5]),(0,[z0,z1,z2,z3,z816,z5]),(0,[z0,z1,z2,z3,z817,z5]),(0,[z0,z1,z3,z818,z7,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z314]),(0,[z0,z2,z3,z58,z819,z5]),(0,[z267,z1,z2,z3,z326,z164]),(0,[z0,z1,z2,z3,z820,z5]),(0,[z0,z1,z2,z3,z7,z821])],[(0,[z0,z1,z107,z99,z7,z5])],[(0,[z0,z1,z2,z3,z7,z822]),(0,[z0,z1,z2,z3,z7,z823]),(0,[z0,z1,z2,z3,z824,z5])],[(0,[z0,z107,z3,z7,z187,z5]),(0,[z0,z1,z2,z3,z7,z825]),(0,[z0,z1,z826,z3,z7,z5]),(0,[z267,z1,z2,z3,z333,z164]),(0,[z0,z1,z827,z3,z7,z5]),(0,[z120,z1,z2,z3,z300,z143])],[(0,[z0,z1,z828,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z829]),(0,[z0,z1,z2,z3,z830,z5])],[(0,[z0,z1,z831,z3,z7,z5]),(0,[z74,z222,z2,z3,z471,z5]),(0,[z38,z1,z39,z3,z7,z314]),(0,[z0,z1,z2,z3,z832,z5]),(0,[z0,z1,z833,z3,z7,z5]),(0,[z0,z114,z718,z3,z7,z5])],[(0,[z0,z1,z2,z3,z7,z168]),(0,[z0,z1,z2,z3,z834,z7]),(0,[z29,z40,z1,z41,z7,z5]),(0,[z29,z1,z132,z41,z7,z5]),(0,[z0,z1,z3,z7,z5,z835]),(0,[z0,z247,z1,z3,z58,z5]),(0,[z0,z248,z2,z3,z58,z5]),(0,[z0,z133,z1,z2,z3,z528]),(0,[z0,z639,z1,z3,z7,z45]),(0,[z0,z1,z2,z3,z836,z5]),(0,[z0,z837,z1,z3,z7,z5]),(0,[z0,z1,z2,z7,z5,z838])],[(0,[z0,z1,z520,z7,z5,z45]),(0,[z0,z1,z2,z839,z7,z5]),(0,[z0,z1,z2,z3,z840,z5]),(0,[z0,z1,z2,z3,z841,z5])]],
   [[(0,[z98,z75,z2,z3,z7,z5]),(0,[z0,z1,z2,z842,z7,z5]),(0,[z0,z1,z2,z3,z7,z843]),(0,[z0,z1,z2,z3,z7,z314]),(0,[z0,z31,z1,z3,z151,z5]),(0,[z0,z1,z3,z7,z5,z844]),(0,[z0,z1,z2,z845,z7,z5]),(0,[z0,z361,z248,z3,z7,z5])],[(0,[z0,z2,z3,z16,z5,z846]),(0,[z0,z1,z2,z63,z58,z64]),(0,[z0,z18,z263,z2,z3,z7]),(0,[z0,z1,z2,z3,z7,z847]),(0,[z0,z44,z1,z3,z7,z254]),(0,[z0,z848,z1,z3,z7,z5]),(0,[z0,z1,z2,z3,z5,z775])],[(0,[z0,z142,z2,z3,z7,z5]),(0,[z0,z1,z2,z7,z849,z5]),(0,[z0,z1,z2,z850,z7,z5]),(0,[z0,z851,z2,z3,z7,z5]),(0,[z166,z0,z287,z1,z3,z5]),(0,[z0,z1,z2,z3,z326,z5])],[(0,[z0,z1,z2,z3,z16,z332]),(0,[z0,z277,z2,z3,z410,z5]),(0,[z0,z2,z3,z16,z852,z5]),(0,[z0,z1,z3,z853,z16,z5]),(0,[z199,z1,z2,z3,z58,z5]),(0,[z0,z1,z2,z3,z854,z5]),(0,[z0,z1,z2,z7,z64,z236])],[(0,[z0,z1,z2,z3,z855,z5]),(0,[z0,z1,z2,z3,z245,z390]),(0,[z0,z856,z1,z3,z7,z5]),(0,[z857,z1,z2,z3,z7,z5])],[(0,[z0,z44,z142,z3,z7,z5]),(0,[z0,z1,z2,z3,z333,z5]),(0,[z0,z858,z1,z2,z3,z5]),(0,[z0,z87,z1,z2,z91,z5]),(0,[z0,z133,z1,z2,z3,z27]),(0,[z0,z195,z1,z2,z17,z5])],[(0,[z0,z1,z3,z859,z7,z5]),(0,[z0,z12,z2,z3,z410,z5]),(0,[z0,z1,z53,z3,z7,z143]),(0,[z0,z1,z156,z3,z7,z5]),(0,[z0,z1,z2,z13,z5,z357])],[(0,[z0,z35,z2,z3,z7,z168]),(0,[z0,z1,z2,z3,z860,z5]),(0,[z0,z1,z2,z3,z17,z775])]],
   [[(0,[z0,z861,z1,z2,z7,z5]),(0,[z0,z1,z2,z3,z7,z862]),(0,[z0,z1,z863,z3,z7,z5]),(0,[z0,z1,z2,z7,z5,z864]),(0,[z0,z19,z1,z8,z58,z5]),(0,[z0,z21,z2,z22,z7,z5])],[(0,[z0,z1,z2,z3,z865,z5]),(0,[z0,z1,z2,z866,z7,z5]),(0,[z29,z1,z2,z41,z30,z5]),(0,[z0,z1,z112,z418,z7,z5])],[(0,[z0,z169,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z867,z5]),(0,[z0,z247,z1,z3,z7,z208]),(0,[z0,z868,z2,z3,z7,z5]),(0,[z0,z1,z2,z16,z5,z46]),(0,[z0,z781,z1,z3,z7,z5]),(0,[z0,z221,z114,z3,z7,z94]),(0,[z0,z1,z2,z7,z5,z869])],[(0,[z0,z44,z1,z520,z7,z5]),(0,[z0,z1,z36,z3,z58,z5]),(0,[z0,z657,z1,z3,z37,z5]),(0,[z0,z870,z1,z2,z7,z5])],[(0,[z0,z1,z2,z3,z134,z332]),(0,[z0,z1,z3,z16,z5,z871]),(0,[z0,z1,z53,z3,z7,z5])],[(0,[z0,z567,z81,z3,z7,z5]),(0,[z0,z1,z2,z3,z872,z5]),(0,[z38,z0,z287,z1,z3,z5]),(0,[z0,z1,z2,z873,z7,z5]),(0,[z0,z2,z3,z58,z178,z5])],[(0,[z166,z1,z341,z3,z7,z5]),(0,[z0,z1,z2,z3,z121,z5]),(0,[z0,z1,z2,z3,z7,z874]),(0,[z0,z48,z2,z126,z49,z7]),(0,[z0,z1,z2,z111,z800,z5]),(0,[z0,z1,z2,z7,z5,z756])],[(0,[z98,z75,z2,z3,z7,z168]),(0,[z0,z875,z2,z3,z7,z5]),(0,[z0,z1,z108,z463,z7,z5]),(0,[z0,z2,z3,z7,z876,z5]),(0,[z0,z1,z3,z7,z790,z5]),(0,[z0,z1,z3,z877,z5,z452])]],
   [[(0,[z0,z1,z2,z377,z7,z64]),(0,[z0,z1,z2,z3,z16,z94]),(0,[z0,z1,z112,z108,z7,z5]),(0,[z0,z119,z1,z7,z197,z45]),(0,[z0,z1,z2,z3,z7,z721]),(0,[z0,z878,z2,z3,z7,z5])],[(0,[z0,z19,z142,z3,z7,z5]),(0,[z0,z142,z108,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z879]),(0,[z0,z1,z2,z3,z880,z5]),(0,[z120,z1,z2,z3,z58,z143]),(0,[z0,z881,z1,z2,z7,z5]),(0,[z0,z1,z2,z3,z7,z882]),(0,[z0,z87,z1,z2,z140,z91])],[],[(0,[z0,z142,z2,z3,z7,z314]),(0,[z0,z200,z1,z3,z7,z5]),(0,[z1,z2,z494,z3,z16,z5])],[(0,[z0,z1,z2,z3,z883,z5]),(0,[z0,z433,z1,z2,z3,z16]),(0,[z0,z35,z36,z3,z7,z138]),(0,[z0,z479,z1,z3,z7,z45]),(0,[z0,z31,z1,z3,z745,z5]),(0,[z0,z87,z433,z1,z2,z3])],[(0,[z0,z884,z1,z2,z16,z5]),(0,[z0,z226,z81,z3,z7,z5]),(0,[z0,z361,z1,z3,z7,z45]),(0,[z885,z0,z1,z3,z7,z5])],[(0,[z0,z40,z1,z7,z64,z5]),(0,[z0,z9,z1,z53,z7,z5]),(0,[z0,z886,z1,z3,z7,z5])],[(0,[z0,z19,z1,z520,z7,z5]),(0,[z29,z1,z2,z41,z7,z5]),(0,[z0,z1,z2,z3,z887,z5]),(0,[z0,z1,z2,z3,z177,z157])]],
   [[(0,[z0,z1,z2,z3,z888,z5]),(0,[z0,z1,z889,z8,z7,z5])],[(0,[z0,z40,z1,z3,z7,z5]),(0,[z0,z1,z2,z149,z7,z314]),(0,[z0,z1,z3,z193,z151,z5]),(0,[z0,z1,z2,z3,z890,z5]),(0,[z0,z1,z2,z3,z891,z5]),(0,[z0,z892,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z5,z893]),(0,[z0,z894,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z895,z5])],[(0,[z0,z1,z2,z3,z7,z896]),(0,[z0,z2,z3,z7,z187,z168]),(0,[z1,z2,z3,z16,z420,z5]),(0,[z146,z1,z2,z3,z789,z5]),(0,[z0,z1,z2,z10,z300,z5]),(0,[z0,z1,z2,z3,z897,z5]),(0,[z0,z898,z1,z2,z3,z7])],[(0,[z0,z1,z2,z3,z203,z332]),(0,[z0,z169,z2,z3,z7,z314]),(0,[z0,z1,z2,z3,z7,z390]),(0,[z0,z1,z833,z3,z58,z5]),(0,[z0,z35,z2,z3,z7,z601]),(0,[z0,z35,z2,z3,z7,z196]),(0,[z0,z899,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z58,z168]),(0,[z0,z900,z1,z2,z3,z5]),(0,[z1,z3,z193,z58,z16,z5]),(0,[z0,z1,z273,z3,z16,z5]),(0,[z0,z901,z1,z2,z7,z5]),(0,[z0,z1,z2,z3,z902,z5])],[(0,[z0,z1,z2,z3,z903,z5]),(0,[z0,z1,z904,z3,z16,z5]),(0,[z0,z1,z2,z3,z905,z5])],[(0,[z0,z906,z1,z3,z7,z5]),(0,[z0,z1,z2,z3,z58,z314]),(0,[z38,z1,z39,z3,z16,z5]),(0,[z77,z1,z2,z78,z7,z390]),(0,[z0,z12,z2,z3,z51,z5]),(0,[z0,z9,z1,z2,z24,z5])],[(0,[z0,z1,z2,z3,z907,z5]),(0,[z0,z908,z2,z3,z7,z5])]],
   [[(0,[z166,z1,z238,z3,z58,z5]),(0,[z120,z1,z2,z230,z7,z143])],[(0,[z0,z1,z3,z37,z151,z5]),(0,[z77,z1,z2,z78,z109,z5]),(0,[z0,z909,z1,z2,z3,z5]),(1,[z0,z1,z3,z7,z721])],[(1,[z1,z2,z736,z7,z5]),(0,[z0,z1,z2,z41,z7,z93]),(0,[z1,z2,z78,z736,z7,z5]),(0,[z42,z1,z2,z3,z16,z5]),(0,[z0,z9,z1,z2,z7,z164])],[(0,[z0,z40,z1,z108,z7,z5]),(0,[z0,z1,z2,z3,z5,z910]),(1,[z1,z2,z3,z789,z5]),(0,[z0,z170,z81,z3,z7,z5])],[(0,[z0,z1,z2,z3,z30,z5]),(0,[z77,z1,z2,z78,z16,z5]),(0,[z0,z80,z81,z3,z16,z5]),(0,[z0,z500,z1,z3,z407,z5]),(0,[z1,z2,z3,z7,z715,z164]),(0,[z0,z1,z3,z7,z115,z45]),(0,[z0,z1,z2,z3,z911,z5])],[(0,[z0,z233,z81,z3,z7,z5]),(0,[z0,z2,z3,z7,z5,z846])],[(0,[z222,z786,z2,z3,z7,z5]),(0,[z0,z912,z1,z3,z7,z5]),(0,[z0,z2,z3,z913,z7,z5]),(0,[z0,z21,z2,z22,z58,z5]),(0,[z0,z1,z2,z58,z5,z46]),(0,[z0,z1,z2,z63,z7,z64])],[(0,[z0,z1,z2,z290,z7,z5]),(0,[z0,z31,z142,z3,z7,z5]),(0,[z120,z247,z1,z3,z7,z143]),(0,[z0,z21,z180,z22,z7,z5])]],
   [[(0,[z0,z868,z2,z3,z58,z5]),(0,[z0,z588,z1,z3,z7,z45]),(0,[z0,z1,z2,z3,z914,z5]),(0,[z0,z433,z1,z2,z111,z7])],[(0,[z0,z1,z2,z3,z915,z5]),(0,[z0,z1,z2,z7,z64,z492]),(0,[z0,z916,z2,z3,z7,z5]),(0,[z0,z195,z133,z1,z2,z3])],[(0,[z0,z1,z2,z917,z7,z5]),(0,[z0,z1,z918,z3,z7,z5]),(0,[z0,z919,z1,z2,z3,z5]),(0,[z0,z1,z53,z3,z58,z5]),(0,[z1,z2,z3,z920,z7,z5]),(0,[z0,z1,z2,z921,z7,z5])],[(0,[z786,z75,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z922]),(0,[z0,z19,z1,z264,z7,z5])],[(0,[z0,z1,z923,z3,z7,z5]),(0,[z0,z924,z1,z3,z7,z5]),(0,[z0,z1,z3,z58,z925,z5])],[(0,[z0,z926,z1,z2,z7,z5]),(0,[z0,z1,z204,z108,z7,z5]),(0,[z0,z35,z81,z3,z7,z45]),(0,[z0,z1,z2,z3,z927,z5]),(0,[z0,z221,z114,z3,z7,z115]),(0,[z0,z133,z1,z2,z73,z3])],[(0,[z0,z1,z107,z3,z16,z5]),(0,[z0,z18,z426,z1,z2,z3])],[(0,[z0,z1,z2,z99,z7,z5]),(0,[z0,z1,z2,z3,z928,z5]),(0,[z0,z1,z2,z3,z929,z5]),(0,[z573,z1,z2,z3,z16,z5]),(0,[z0,z881,z1,z2,z58,z5]),(0,[z930,z1,z2,z3,z7,z5])]],
   [[(0,[z0,z9,z1,z2,z16,z5]),(0,[z0,z1,z2,z16,z5,z197]),(0,[z0,z44,z1,z3,z7,z115]),(0,[z0,z1,z931,z3,z7,z5])],[(0,[z0,z1,z932,z3,z7,z5]),(0,[z166,z1,z3,z425,z7,z5]),(0,[z0,z18,z40,z1,z7,z5]),(0,[z239,z1,z2,z3,z16,z5]),(0,[z0,z1,z933,z3,z7,z5]),(0,[z0,z103,z1,z3,z37,z5]),(0,[z0,z133,z1,z2,z3,z676])],[(0,[z0,z31,z1,z3,z193,z5]),(0,[z0,z934,z1,z3,z7,z5])],[(0,[z0,z174,z2,z3,z51,z5])],[(0,[z0,z142,z2,z3,z16,z5]),(0,[z0,z18,z1,z2,z7,z271]),(1,[z1,z2,z3,z7,z715]),(0,[z0,z114,z248,z3,z7,z5])],[(0,[z0,z1,z2,z3,z16,z140]),(0,[z0,z1,z3,z37,z745,z5]),(0,[z0,z1,z2,z935,z7,z5]),(0,[z0,z936,z1,z3,z7,z5])],[(0,[z0,z359,z1,z2,z135,z5]),(0,[z0,z937,z1,z2,z7,z5]),(0,[z120,z1,z2,z3,z7,z143])],[(0,[z0,z1,z107,z3,z134,z5]),(0,[z0,z1,z2,z3,z15,z5]),(0,[z0,z1,z2,z3,z938,z5]),(0,[z0,z19,z1,z889,z7,z5])]],
   [[(0,[z98,z75,z2,z290,z7,z5]),(0,[z74,z222,z2,z3,z58,z5]),(0,[z0,z1,z156,z3,z16,z5]),(0,[z0,z1,z2,z3,z7,z939]),(0,[z0,z1,z940,z3,z7,z5]),(0,[z0,z18,z1,z2,z627,z7])],[(0,[z0,z1,z2,z3,z58,z390]),(0,[z0,z221,z114,z3,z58,z5]),(0,[z0,z941,z1,z3,z7,z5]),(0,[z0,z1,z2,z3,z942,z5]),(0,[z0,z1,z943,z3,z7,z5])],[(0,[z0,z1,z2,z149,z16,z5]),(0,[z0,z18,z1,z2,z16,z131]),(0,[z0,z71,z1,z3,z16,z5]),(0,[z0,z1,z2,z3,z7,z944]),(0,[z0,z1,z2,z3,z945,z5])],[(0,[z0,z1,z2,z230,z121,z5]),(0,[z0,z946,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z947,z5]),(0,[z0,z1,z2,z948,z7,z5])],[(0,[z0,z1,z2,z3,z949,z5]),(0,[z38,z1,z39,z3,z478,z5]),(0,[z0,z1,z3,z7,z93,z950]),(0,[z0,z262,z2,z3,z281,z5]),(0,[z0,z44,z1,z3,z58,z181]),(0,[z0,z48,z2,z810,z7,z5]),(0,[z0,z436,z21,z22,z7,z5]),(0,[z0,z1,z951,z3,z7,z5])],[(0,[z0,z1,z2,z520,z7,z208]),(0,[z1,z2,z3,z16,z503,z5]),(0,[z0,z361,z1,z3,z7,z115]),(0,[z952,z1,z2,z3,z7,z5])],[(0,[z0,z953,z1,z3,z7,z5]),(0,[z0,z1,z954,z3,z7,z5]),(0,[z0,z142,z3,z7,z5,z45]),(0,[z0,z1,z3,z7,z5,z452]),(0,[z0,z1,z2,z736,z7,z5]),(0,[z0,z1,z2,z78,z7,z93]),(0,[z0,z1,z2,z3,z7,z775])],[(0,[z0,z1,z2,z3,z7,z955]),(0,[z0,z956,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z789,z5]),(0,[z0,z152,z1,z2,z3,z305])]],
   [[(0,[z98,z75,z2,z99,z7,z5]),(0,[z0,z1,z2,z3,z957,z5]),(0,[z0,z1,z2,z958,z7,z5]),(0,[z42,z1,z2,z3,z789,z5]),(0,[z0,z1,z180,z3,z16,z5]),(0,[z0,z959,z1,z2,z3,z5])],[(0,[z0,z1,z338,z3,z7,z332]),(0,[z0,z1,z2,z960,z7,z5]),(0,[z0,z114,z287,z1,z3,z5]),(0,[z0,z1,z961,z3,z7,z5]),(0,[z0,z87,z1,z2,z627,z5]),(0,[z0,z1,z962,z3,z7,z5])],[(0,[z0,z1,z2,z3,z963,z5]),(0,[z0,z1,z112,z108,z16,z5]),(0,[z0,z48,z152,z2,z49,z7]),(0,[z0,z12,z2,z3,z442,z5]),(0,[z0,z1,z2,z3,z964,z5]),(0,[z0,z119,z1,z3,z7,z45]),(0,[z0,z119,z1,z3,z7,z721])],[(0,[z0,z965,z2,z3,z7,z5]),(0,[z0,z966,z2,z3,z7,z5]),(0,[z0,z441,z114,z3,z7,z5]),(0,[z635,z1,z238,z3,z7,z5]),(0,[z1,z2,z3,z16,z519,z5]),(0,[z0,z2,z3,z7,z819,z5]),(0,[z0,z1,z2,z3,z967,z5]),(0,[z0,z1,z2,z3,z7,z968]),(0,[z0,z87,z1,z2,z292,z5])],[(0,[z0,z1,z2,z3,z7,z969]),(0,[z0,z1,z2,z970,z7,z5]),(0,[z0,z1,z971,z3,z58,z5]),(0,[z0,z912,z1,z3,z58,z5]),(0,[z0,z247,z1,z3,z7,z45]),(0,[z0,z972,z2,z3,z7,z5]),(0,[z0,z1,z973,z3,z7,z5]),(0,[z0,z1,z2,z3,z177,z775])],[(0,[z0,z1,z2,z290,z58,z5]),(0,[z74,z222,z2,z3,z237,z5]),(0,[z166,z1,z238,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z974]),(0,[z0,z200,z1,z3,z16,z5]),(0,[z0,z200,z1,z3,z37,z5]),(0,[z0,z975,z2,z3,z7,z5])],[(0,[z0,z1,z107,z3,z203,z5]),(0,[z42,z200,z1,z3,z16,z5]),(0,[z0,z1,z2,z3,z5,z976])],[(0,[z0,z1,z2,z3,z977,z5]),(0,[z0,z978,z1,z3,z7,z5]),(0,[z0,z979,z1,z2,z3,z5]),(0,[z0,z413,z2,z3,z7,z187]),(0,[z0,z18,z1,z2,z489,z7])]],
   [[(0,[z0,z1,z3,z7,z208,z45]),(0,[z0,z35,z2,z3,z16,z138]),(0,[z1,z2,z3,z980,z7,z5]),(0,[z0,z35,z1,z53,z3,z7]),(0,[z0,z133,z1,z2,z46,z27])],[(0,[z0,z1,z981,z3,z7,z5]),(0,[z29,z1,z2,z41,z16,z5]),(0,[z396,z1,z2,z78,z7,z5]),(0,[z0,z1,z2,z3,z58,z922]),(0,[z0,z1,z2,z3,z5,z403])],[(1,[z1,z714,z3,z7,z5]),(0,[z0,z1,z112,z889,z7,z5]),(0,[z0,z87,z1,z2,z800,z5])],[(0,[z0,z1,z2,z3,z16,z208]),(0,[z0,z40,z1,z3,z16,z5]),(0,[z0,z1,z132,z3,z16,z5]),(0,[z0,z941,z263,z3,z7,z5]),(0,[z0,z361,z35,z3,z7,z138]),(1,[z0,z1,z2,z3,z775])],[(0,[z0,z1,z2,z3,z471,z5]),(0,[z0,z1,z982,z3,z7,z5]),(0,[z0,z1,z2,z58,z5,z197])],[(0,[z0,z1,z2,z99,z58,z5]),(0,[z0,z983,z2,z3,z7,z5])],[(0,[z0,z1,z2,z520,z4,z5]),(0,[z0,z984,z1,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z985]),(0,[z0,z1,z2,z230,z16,z5]),(0,[z0,z152,z1,z2,z3,z16]),(0,[z267,z2,z3,z7,z178,z164]),(0,[z0,z247,z983,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z986]),(0,[z0,z1,z2,z3,z987,z5]),(1,[z0,z1,z2,z800,z5])],[(0,[z0,z1,z2,z10,z7,z143]),(0,[z0,z1,z988,z3,z7,z5])]],
   [[(0,[z0,z1,z2,z3,z7,z989]),(0,[z0,z1,z2,z3,z245,z93]),(0,[z0,z1,z2,z3,z7,z715]),(0,[z0,z1,z2,z3,z7,z990]),(0,[z0,z1,z2,z991,z7,z5]),(0,[z0,z18,z1,z2,z403,z131])],[(0,[z0,z1,z992,z3,z7,z5]),(0,[z0,z1,z2,z993,z7,z5]),(0,[z0,z50,z2,z3,z281,z5]),(0,[z0,z1,z2,z3,z994,z5])],[(0,[z0,z1,z2,z3,z995,z5]),(0,[z0,z761,z1,z3,z16,z5]),(0,[z0,z1,z2,z63,z7,z246]),(0,[z0,z35,z459,z2,z3,z7]),(0,[z0,z1,z2,z3,z24,z5]),(0,[z0,z426,z1,z2,z64,z5])],[(0,[z38,z1,z39,z520,z7,z5])],[(0,[z0,z996,z1,z2,z3,z5]),(0,[z0,z1,z3,z7,z440,z45]),(0,[z0,z1,z997,z3,z7,z5]),(0,[z0,z1,z2,z3,z998,z5])],[(0,[z0,z1,z2,z3,z999,z5]),(0,[z0,z1,z2,z3,z7,z1000]),(0,[z0,z1001,z2,z3,z7,z5]),(0,[z0,z1,z2,z10,z7,z5]),(0,[z0,z247,z1,z3,z16,z5]),(0,[z1,z2,z664,z3,z16,z5]),(0,[z0,z248,z2,z3,z16,z5]),(0,[z120,z1,z2,z3,z121,z143]),(0,[z0,z1,z2,z3,z1002,z5])],[(0,[z0,z1,z2,z520,z7,z5]),(0,[z0,z1,z2,z1003,z7,z5]),(0,[z0,z1,z2,z1004,z7,z5]),(0,[z0,z1,z2,z3,z1005,z5]),(0,[z0,z1,z2,z3,z1006,z5])],[(0,[z0,z1007,z1,z2,z3,z7]),(0,[z0,z1,z2,z3,z7,z1008]),(0,[z0,z1,z2,z3,z1009,z5]),(0,[z0,z195,z133,z1,z2,z27])]],
   [[(0,[z0,z1,z107,z3,z7,z332]),(0,[z0,z1,z2,z3,z1010,z5]),(0,[z0,z2,z3,z7,z178,z5]),(0,[z0,z1,z2,z149,z478,z5]),(0,[z0,z1011,z2,z3,z7,z5]),(0,[z0,z1,z2,z63,z16,z64])],[(0,[z0,z1,z2,z1012,z7,z5]),(0,[z0,z1,z2,z3,z7,z1013]),(0,[z0,z1014,z2,z3,z7,z5]),(0,[z0,z1,z3,z37,z4,z5]),(0,[z0,z1,z3,z193,z7,z5]),(0,[z0,z1015,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z1016,z5]),(0,[z267,z1,z2,z3,z16,z164]),(0,[z599,z1,z2,z3,z16,z5]),(0,[z0,z195,z1,z2,z58,z5]),(0,[z0,z48,z2,z305,z49,z5]),(0,[z0,z1,z2,z3,z1017,z5])],[(0,[z0,z1,z2,z3,z7,z1018]),(0,[z74,z786,z2,z3,z7,z5]),(0,[z0,z1019,z1,z3,z7,z5]),(0,[z166,z1,z3,z7,z5,z525]),(1,[z0,z718,z3,z7,z5]),(0,[z1020,z1,z2,z3,z7,z5]),(0,[z0,z1,z1021,z3,z7,z5])],[(0,[z0,z1,z2,z3,z1022,z5]),(0,[z0,z1,z2,z3,z7,z1023]),(0,[z0,z152,z1,z1024,z3,z7]),(0,[z0,z1,z2,z1025,z7,z5])],[(0,[z74,z222,z2,z3,z7,z5]),(0,[z1,z786,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z1026,z7]),(0,[z0,z1,z2,z3,z877,z5]),(0,[z0,z2,z81,z3,z7,z115]),(0,[z0,z1027,z1,z2,z3,z5])],[(0,[z1,z2,z3,z425,z58,z5]),(0,[z0,z221,z114,z3,z7,z5]),(0,[z0,z1,z2,z3,z126,z7]),(0,[z0,z1,z2,z3,z1028,z5]),(0,[z1029,z1,z2,z3,z7,z5])],[(0,[z0,z1,z2,z7,z5,z1030]),(0,[z0,z19,z1,z8,z16,z5]),(0,[z1,z2,z3,z428,z58,z5]),(0,[z0,z1,z2,z3,z1031,z5])]],
   [[(0,[z0,z2,z3,z7,z5,z1032]),(0,[z1,z2,z3,z789,z16,z5]),(0,[z0,z119,z1,z3,z58,z45])],[(0,[z0,z1,z2,z3,z109,z5]),(0,[z0,z215,z1,z3,z193,z5]),(0,[z0,z1,z2,z3,z1033,z5]),(0,[z0,z44,z1,z3,z7,z181])],[(0,[z0,z1,z2,z3,z7,z1034]),(0,[z0,z1,z36,z3,z16,z5]),(0,[z0,z1,z2,z1035,z7,z5]),(0,[z0,z1,z2,z3,z5,z1036]),(0,[z0,z1,z2,z3,z7,z1037]),(0,[z0,z1,z2,z1038,z7,z5]),(0,[z0,z426,z1,z2,z63,z3])],[(0,[z0,z1,z2,z1039,z7,z5]),(0,[z0,z795,z2,z3,z16,z5]),(0,[z110,z1,z2,z3,z7,z164]),(0,[z0,z18,z1,z53,z7,z131])],[(0,[z0,z1,z2,z3,z16,z5]),(0,[z0,z796,z1,z3,z16,z5]),(0,[z0,z433,z1,z2,z3,z58]),(0,[z1040,z1,z2,z3,z7,z5]),(0,[z0,z2,z810,z49,z7,z5]),(0,[z0,z1041,z1,z3,z7,z5]),(0,[z0,z1042,z1,z3,z7,z5])],[(0,[z0,z1,z108,z520,z7,z5]),(0,[z0,z1,z2,z3,z1043,z5]),(0,[z0,z1044,z1,z2,z3,z5]),(0,[z0,z216,z1,z2,z3,z257])],[(0,[z0,z1,z714,z3,z7,z5]),(0,[z0,z1,z1045,z3,z7,z5]),(0,[z687,z1,z2,z3,z16,z5]),(0,[z0,z1046,z2,z3,z58,z5]),(0,[z0,z1041,z152,z1,z3,z7]),(0,[z0,z1,z1047,z3,z7,z5])],[(0,[z0,z1,z1048,z3,z7,z5]),(0,[z166,z0,z9,z1,z7,z5]),(0,[z0,z1,z2,z3,z7,z93]),(0,[z0,z1,z2,z3,z1049,z5]),(0,[z0,z805,z2,z3,z16,z5]),(0,[z0,z1,z2,z3,z1050,z5]),(0,[z0,z1,z2,z63,z343,z7])]],
   [[(0,[z0,z1,z1051,z3,z7,z5]),(0,[z120,z1,z2,z3,z16,z143]),(0,[z235,z1,z2,z3,z16,z5]),(0,[z0,z1,z2,z3,z305,z5])],[(0,[z0,z1,z2,z3,z58,z332]),(0,[z0,z1,z2,z3,z7,z1052]),(0,[z0,z142,z2,z520,z7,z5]),(0,[z0,z1,z2,z3,z478,z208]),(0,[z0,z1,z971,z3,z7,z5]),(0,[z0,z48,z2,z49,z7,z5])],[(0,[z0,z142,z39,z3,z7,z5]),(0,[z0,z2,z3,z7,z852,z5]),(0,[z77,z1,z2,z78,z7,z93]),(0,[z77,z1,z2,z736,z7,z5])],[(0,[z0,z1,z2,z3,z1053,z5]),(0,[z0,z1,z2,z3,z1054,z5]),(0,[z0,z1055,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z1056,z5]),(0,[z0,z1,z2,z1057,z7,z5]),(0,[z0,z1,z2,z3,z1058,z5])],[(0,[z0,z1,z2,z3,z151,z5]),(0,[z0,z1,z2,z7,z756,z131])],[(0,[z0,z1,z2,z3,z134,z5]),(0,[z0,z31,z1,z3,z258,z5]),(0,[z0,z1059,z1,z2,z3,z5]),(0,[z0,z1,z2,z810,z7,z5])],[(0,[z0,z1,z1060,z3,z7,z5]),(0,[z0,z1,z771,z3,z7,z5]),(0,[z344,z1,z2,z3,z16,z5]),(0,[z267,z263,z2,z3,z7,z164]),(0,[z0,z436,z1,z3,z7,z5]),(0,[z0,z361,z1,z3,z7,z5]),(0,[z0,z361,z1,z3,z7,z181]),(0,[z0,z1,z2,z7,z64,z756])],[(0,[z0,z1061,z1,z3,z7,z5]),(0,[z0,z263,z2,z3,z7,z187]),(0,[z0,z1,z2,z1062,z7,z5]),(0,[z0,z1,z2,z3,z1063,z5]),(0,[z0,z1,z2,z3,z1064,z5])]],
   [[(0,[z0,z1,z2,z3,z7,z1065]),(0,[z0,z1,z826,z3,z16,z5]),(0,[z1066,z1,z2,z3,z7,z5]),(0,[z0,z18,z426,z1,z2,z131])],[(0,[z0,z169,z2,z520,z7,z5]),(0,[z0,z1,z1067,z3,z7,z5]),(0,[z0,z1068,z1,z2,z3,z7]),(0,[z0,z2,z22,z810,z7,z5]),(0,[z0,z12,z2,z3,z730,z5]),(0,[z0,z87,z1,z2,z398,z5]),(0,[z0,z1,z2,z7,z5,z46]),(0,[z0,z1,z1069,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z756])],[(0,[z38,z0,z9,z1,z7,z5]),(0,[z0,z200,z1,z3,z104,z5]),(0,[z0,z1,z2,z1070,z7,z5]),(0,[z0,z221,z718,z3,z7,z5]),(0,[z0,z1,z2,z13,z34,z5]),(0,[z0,z1,z2,z3,z1071,z5]),(0,[z0,z133,z1,z2,z3,z292])],[(0,[z0,z1,z1072,z3,z7,z5]),(0,[z0,z1,z2,z1073,z7,z5]),(0,[z0,z1,z2,z3,z16,z168]),(0,[z0,z1074,z1,z3,z7,z5]),(0,[z0,z1,z3,z7,z5,z871]),(0,[z0,z1,z2,z10,z58,z5]),(0,[z0,z1075,z2,z3,z7,z5])],[(0,[z0,z75,z107,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z1076]),(0,[z0,z1,z3,z7,z5,z1077]),(0,[z0,z142,z3,z37,z7,z5]),(0,[z0,z1,z2,z520,z58,z5]),(0,[z0,z1,z2,z3,z7,z1078]),(0,[z0,z1,z2,z1079,z7,z5]),(0,[z1080,z1,z2,z3,z7,z5])],[(0,[z98,z75,z2,z3,z16,z5]),(0,[z0,z1,z2,z3,z16,z314]),(0,[z26,z1,z2,z3,z16,z5]),(0,[z0,z1081,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z1082,z5]),(0,[z0,z2,z3,z51,z730,z5])],[(1,[z786,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z1083,z7]),(0,[z0,z1084,z1,z3,z7,z5]),(0,[z1,z2,z280,z3,z16,z5]),(0,[z0,z2,z3,z810,z7,z5]),(0,[z0,z1,z2,z889,z7,z5])],[(0,[z0,z1085,z2,z3,z7,z5]),(0,[z0,z1,z2,z1086,z7,z5]),(0,[z0,z1,z2,z3,z1087,z5]),(0,[z0,z1,z1088,z3,z7,z5]),(0,[z0,z1,z3,z7,z925,z5]),(0,[z0,z1,z3,z193,z58,z5]),(0,[z0,z537,z1,z2,z514,z5])]],
   [[(0,[z0,z263,z2,z3,z7,z5]),(0,[z212,z75,z2,z3,z7,z5]),(0,[z0,z263,z2,z3,z7,z181]),(0,[z0,z1089,z1,z3,z7,z5])],[(0,[z0,z1,z2,z3,z7,z1090]),(0,[z0,z1,z2,z290,z7,z168]),(0,[z599,z1,z2,z78,z7,z5]),(0,[z0,z1,z2,z3,z7,z1091]),(0,[z0,z1,z2,z3,z1092,z5])],[(0,[z0,z793,z1,z2,z3,z16]),(0,[z0,z1,z2,z3,z7,z1093])],[(0,[z0,z31,z1,z3,z4,z5]),(0,[z0,z1,z3,z859,z16,z5]),(0,[z0,z1,z2,z3,z7,z115]),(0,[z0,z18,z1,z2,z7,z437])],[(0,[z0,z1,z2,z3,z203,z5]),(0,[z0,z1,z1094,z3,z7,z5]),(0,[z0,z1,z2,z3,z134,z168]),(0,[z0,z1095,z2,z3,z7,z5]),(1,[z0,z2,z810,z7,z5]),(0,[z0,z1,z2,z3,z7,z1096]),(0,[z0,z1,z3,z7,z721,z5]),(0,[z0,z1,z1097,z3,z7,z5]),(0,[z0,z195,z1,z2,z177,z7])],[(0,[z0,z1,z338,z3,z58,z5]),(0,[z0,z1,z2,z3,z7,z1098]),(0,[z0,z1099,z2,z3,z7,z5]),(0,[z0,z21,z2,z22,z16,z5]),(0,[z0,z1100,z1,z2,z7,z5]),(0,[z0,z50,z2,z3,z730,z5])],[(0,[z98,z75,z2,z3,z134,z5]),(0,[z0,z216,z200,z1,z3,z5]),(0,[z0,z1,z2,z3,z126,z58]),(0,[z0,z1,z1101,z3,z58,z5]),(0,[z0,z218,z2,z3,z7,z5]),(0,[z0,z1,z1102,z3,z7,z5])],[(0,[z0,z35,z107,z3,z7,z5]),(0,[z0,z169,z2,z3,z16,z5]),(0,[z0,z726,z1,z2,z3,z7]),(0,[z0,z195,z1,z2,z7,z5])]],
   [[(0,[z0,z1,z2,z3,z1103,z5]),(0,[z0,z1,z2,z3,z7,z1104]),(0,[z0,z40,z1,z520,z7,z5]),(0,[z0,z1,z2,z3,z5,z1105]),(0,[z349,z1,z2,z3,z58,z5]),(0,[z0,z18,z1,z2,z7,z453]),(0,[z0,z361,z81,z3,z7,z5]),(0,[z0,z1106,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z745,z5])],[(0,[z0,z1,z2,z3,z7,z1107]),(0,[z0,z1,z2,z99,z7,z168]),(0,[z0,z1,z53,z3,z16,z5]),(0,[z0,z540,z81,z3,z7,z5])],[(0,[z0,z1,z2,z3,z478,z5]),(0,[z306,z1,z2,z3,z16,z5]),(0,[z0,z1,z273,z3,z58,z5]),(0,[z0,z1108,z1,z2,z3,z5])],[(0,[z38,z23,z1,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z1109]),(0,[z0,z1,z2,z13,z111,z5])],[(0,[z0,z1,z2,z3,z7,z1110]),(0,[z0,z1,z1111,z3,z7,z5]),(0,[z0,z263,z827,z3,z7,z5]),(0,[z0,z18,z1,z2,z7,z631])],[(0,[z0,z1,z2,z3,z58,z93]),(0,[z0,z1,z2,z3,z229,z59]),(0,[z0,z1,z2,z1112,z7,z5]),(0,[z0,z1,z108,z889,z7,z5])],[(0,[z0,z1,z2,z3,z1113,z5]),(0,[z0,z1,z2,z3,z7,z1114]),(0,[z0,z200,z1,z3,z113,z5]),(0,[z0,z56,z1,z2,z3,z528]),(0,[z0,z1,z2,z3,z1115,z5]),(0,[z0,z1116,z1,z3,z7,z5])],[(0,[z0,z48,z2,z49,z58,z5]),(1,[z0,z1,z889,z7,z5]),(0,[z0,z248,z2,z3,z7,z45]),(0,[z0,z433,z1,z2,z3,z7])]],
   [[],[(0,[z98,z213,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z1117,z5]),(0,[z38,z573,z1,z3,z7,z5])],[(0,[z0,z1,z2,z3,z1118,z5]),(0,[z0,z18,z1,z2,z7,z643]),(0,[z0,z1,z2,z3,z1119,z5]),(0,[z0,z1,z2,z3,z1120,z5])],[(0,[z0,z1,z2,z3,z203,z168]),(0,[z0,z44,z1,z3,z7,z208]),(0,[z0,z1046,z2,z3,z7,z5])],[(0,[z1,z2,z3,z16,z5,z690]),(0,[z0,z436,z1,z3,z58,z5]),(0,[z0,z361,z1,z3,z58,z5]),(0,[z345,z1,z2,z3,z58,z5]),(0,[z404,z1,z2,z3,z7,z164])],[(0,[z98,z75,z2,z3,z203,z5]),(0,[z0,z1,z2,z3,z7,z1121]),(0,[z166,z1,z238,z3,z15,z5]),(0,[z0,z152,z1,z2,z41,z7]),(0,[z0,z1,z2,z3,z109,z390]),(0,[z0,z1,z2,z24,z5,z197])],[(0,[z0,z1,z2,z3,z7,z332]),(0,[z0,z1,z2,z3,z7,z1122]),(0,[z0,z1,z3,z853,z7,z5]),(0,[z120,z1,z3,z7,z143,z452])],[]],
   [[(0,[z0,z1,z2,z3,z16,z390]),(0,[z0,z1,z3,z7,z5,z950]),(0,[z0,z1,z2,z3,z1123,z5]),(0,[z0,z1,z2,z3,z1124,z5]),(0,[z0,z1125,z2,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z1126]),(0,[z0,z287,z1,z2,z3,z5]),(0,[z0,z103,z1,z3,z745,z5]),(0,[z0,z426,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z7,z1127]),(0,[z200,z1,z3,z58,z16,z5]),(0,[z0,z1,z2,z58,z5,z760]),(0,[z0,z1,z2,z3,z1128,z5]),(1,[z0,z1,z3,z745,z5])],[(0,[z0,z786,z2,z3,z7,z5]),(0,[z265,z1,z2,z3,z16,z5]),(0,[z0,z114,z561,z3,z7,z5])],[(0,[z0,z1,z2,z3,z478,z314]),(0,[z38,z614,z1,z3,z7,z5]),(0,[z0,z1,z2,z388,z89,z5]),(0,[z0,z1081,z2,z3,z58,z5]),(0,[z0,z1,z2,z3,z7,z1129]),(0,[z0,z18,z1,z2,z7,z756])],[(0,[z0,z1,z107,z3,z58,z5])],[(0,[z0,z142,z2,z3,z478,z5]),(0,[z0,z1,z2,z3,z245,z5]),(0,[z0,z165,z81,z3,z7,z5]),(0,[z1130,z1,z2,z3,z7,z5])],[(0,[z0,z1,z2,z3,z7,z1131]),(0,[z0,z1,z2,z3,z1132,z5]),(0,[z0,z40,z1,z8,z7,z5]),(0,[z0,z1,z2,z3,z5,z1133]),(0,[z0,z263,z2,z3,z58,z5]),(0,[z0,z9,z1,z2,z58,z5]),(0,[z1134,z1,z2,z3,z7,z5]),(0,[z0,z103,z1,z3,z5,z399])],[(0,[z0,z1,z2,z3,z1135,z5]),(0,[z547,z1,z2,z3,z16,z5]),(0,[z0,z1,z2,z7,z5,z197]),(0,[z0,z1,z2,z7,z1136,z5])]],
   [[(0,[z0,z1,z2,z3,z1137,z5]),(0,[z77,z1,z2,z78,z245,z5]),(0,[z362,z1,z2,z3,z58,z5])],[(0,[z0,z1,z3,z16,z5,z844]),(0,[z0,z200,z1,z3,z17,z5]),(0,[z0,z1,z2,z3,z58,z115]),(0,[z0,z500,z1,z3,z37,z5]),(0,[z0,z1,z2,z1138,z7,z5]),(0,[z0,z1,z2,z3,z1139,z5])],[(0,[z0,z1,z2,z3,z7,z731]),(0,[z0,z31,z1,z555,z3,z5]),(1,[z0,z18,z426,z1,z2])],[(0,[z0,z1,z2,z16,z849,z5]),(0,[z0,z1,z2,z3,z7,z94])],[(0,[z0,z1,z2,z290,z16,z5]),(0,[z0,z1,z2,z3,z1140,z5]),(0,[z0,z1141,z2,z3,z7,z5]),(0,[z0,z565,z2,z3,z382,z5]),(0,[z0,z218,z2,z3,z58,z5]),(0,[z120,z1,z2,z10,z7,z143]),(0,[z0,z1,z1024,z3,z7,z5])],[(0,[z0,z169,z2,z3,z478,z5]),(0,[z120,z1,z2,z3,z7,z715]),(0,[z0,z9,z1,z8,z7,z5])],[(0,[z82,z222,z2,z3,z7,z5]),(0,[z186,z1,z2,z3,z16,z5]),(0,[z0,z152,z1,z2,z3,z58]),(0,[z485,z1,z2,z3,z58,z5]),(0,[z0,z1,z2,z230,z300,z5]),(0,[z0,z1,z2,z7,z5,z1142]),(0,[z0,z1,z2,z63,z7,z592])],[(0,[z98,z75,z2,z3,z7,z332]),(0,[z0,z1,z2,z3,z1143,z5]),(0,[z0,z1,z2,z3,z7,z1144]),(0,[z0,z1,z739,z3,z7,z5]),(0,[z0,z718,z80,z3,z7,z5])]],
   [[(0,[z0,z884,z1,z2,z7,z5]),(0,[z0,z1,z2,z1145,z7,z5]),(0,[z213,z1,z2,z3,z16,z5]),(0,[z0,z31,z1,z3,z572,z5]),(0,[z0,z1,z1146,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z1147]),(0,[z0,z1,z2,z3,z1148,z5]),(0,[z0,z1,z2,z3,z17,z289])],[(0,[z0,z222,z107,z3,z7,z5]),(0,[z38,z1,z39,z3,z4,z5]),(0,[z0,z1,z2,z3,z1149,z5]),(0,[z0,z1061,z1,z3,z16,z5]),(0,[z0,z1,z2,z16,z5,z864]),(0,[z0,z221,z2,z3,z7,z115])],[(0,[z0,z1,z338,z3,z7,z5]),(0,[z1,z2,z3,z58,z789,z5]),(0,[z0,z35,z2,z3,z7,z301]),(0,[z0,z1,z2,z3,z800,z5])],[(0,[z175,z1,z2,z3,z16,z5]),(0,[z0,z1,z1101,z3,z7,z5])],[(0,[z0,z1,z2,z99,z16,z5]),(0,[z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z1150,z3,z7,z5]),(0,[z0,z1,z2,z3,z177,z17])],[(0,[z0,z1,z2,z290,z134,z5]),(0,[z0,z1,z2,z1151,z7,z5]),(0,[z656,z1,z2,z78,z7,z5]),(0,[z146,z1,z2,z3,z58,z5]),(0,[z0,z1152,z1,z2,z3,z5]),(0,[z0,z1,z2,z1153,z7,z5]),(0,[z0,z1154,z2,z3,z7,z5])],[(0,[z0,z19,z1,z53,z7,z5])],[(0,[z0,z1,z2,z3,z1026,z16]),(0,[z598,z1,z2,z3,z58,z5]),(0,[z0,z1,z273,z3,z7,z5])]],
   [[(0,[z0,z1,z904,z3,z7,z5]),(0,[z0,z1,z2,z3,z1155,z5]),(0,[z0,z1,z2,z3,z5,z1156]),(0,[z0,z1,z2,z3,z1157,z5])],[(0,[z38,z1,z39,z3,z7,z5])],[(0,[z0,z1,z2,z520,z7,z314]),(0,[z0,z1158,z1,z2,z3,z5]),(0,[z0,z1,z2,z388,z111,z5]),(0,[z1159,z1,z2,z3,z7,z5])],[(0,[z0,z1,z2,z1160,z7,z5]),(0,[z0,z1,z1161,z3,z7,z5]),(0,[z0,z221,z421,z3,z7,z5]),(0,[z0,z1,z2,z1162,z7,z5]),(0,[z29,z1,z2,z736,z7,z5]),(0,[z0,z937,z1,z2,z16,z5]),(0,[z0,z1059,z1,z3,z5,z452])],[(0,[z0,z65,z152,z1,z2,z3]),(0,[z0,z1,z3,z7,z181,z721])],[(0,[z0,z1,z2,z99,z134,z5]),(0,[z0,z1163,z1,z2,z3,z7]),(0,[z166,z1,z714,z3,z7,z5]),(0,[z0,z247,z1075,z3,z7,z5]),(0,[z0,z65,z1,z2,z3,z5])],[(0,[z0,z1164,z2,z3,z7,z5]),(0,[z0,z103,z1,z3,z193,z5]),(0,[z0,z2,z3,z7,z730,z5])],[(0,[z0,z1,z2,z3,z76,z5]),(0,[z77,z1,z2,z78,z7,z5]),(0,[z0,z1,z2,z3,z1165,z5]),(0,[z0,z1,z1166,z3,z7,z5]),(0,[z0,z87,z18,z133,z1,z2])]],
   [[],[(0,[z0,z1,z338,z3,z7,z168]),(0,[z0,z195,z1,z2,z16,z5]),(0,[z0,z718,z2,z3,z7,z5]),(0,[z0,z50,z2,z3,z88,z5]),(0,[z0,z1,z3,z889,z7,z5])],[(0,[z0,z747,z1,z2,z3,z58]),(0,[z0,z1167,z1,z3,z7,z5])],[(0,[z98,z75,z338,z3,z7,z5]),(0,[z0,z1,z2,z1168,z7,z5]),(0,[z0,z718,z1,z3,z7,z5])],[(0,[z0,z1,z2,z290,z203,z5]),(0,[z0,z1169,z2,z3,z7,z5]),(0,[z0,z1170,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z300,z5]),(0,[z0,z565,z2,z3,z88,z5]),(0,[z1171,z1,z2,z3,z7,z5]),(0,[z0,z133,z1,z2,z3,z775])],[(0,[z0,z1,z2,z1172,z7,z5]),(0,[z0,z9,z1,z2,z7,z143]),(0,[z0,z1,z2,z3,z1173,z5])],[(0,[z0,z1,z2,z3,z1174,z5]),(0,[z0,z1,z53,z3,z7,z164]),(0,[z239,z1,z2,z3,z7,z143]),(0,[z0,z71,z12,z3,z51,z5]),(0,[z0,z1,z2,z3,z1175,z5]),(0,[z0,z1176,z2,z3,z7,z5]),(0,[z0,z1177,z2,z3,z7,z5])],[(0,[z0,z142,z2,z3,z4,z5]),(0,[z0,z119,z1,z3,z16,z45]),(0,[z0,z1,z2,z10,z121,z5]),(0,[z0,z287,z1,z81,z3,z5]),(0,[z0,z1,z2,z1178,z7,z5]),(0,[z0,z1179,z1,z2,z3,z7]),(0,[z0,z1,z1180,z3,z7,z5]),(0,[z0,z195,z133,z1,z2,z5])]],
   [[(0,[z38,z1,z714,z3,z7,z5]),(0,[z0,z244,z2,z49,z7,z5]),(0,[z0,z1181,z1,z3,z7,z5]),(0,[z0,z1,z112,z7,z5,z232]),(0,[z0,z1,z2,z1182,z7,z5])],[(0,[z0,z1,z107,z3,z7,z5]),(0,[z0,z1,z2,z3,z7,z1183]),(0,[z0,z1,z2,z3,z58,z94]),(0,[z0,z1,z112,z53,z7,z5]),(0,[z0,z133,z1,z2,z3,z550])],[(0,[z0,z1,z1184,z3,z7,z5]),(0,[z166,z1,z238,z3,z16,z5]),(0,[z0,z1185,z1,z2,z3,z5]),(0,[z0,z287,z1,z2,z5,z197])],[(0,[z0,z1,z2,z3,z1186,z5]),(0,[z0,z1,z2,z3,z1187,z5]),(0,[z1,z2,z3,z16,z176,z5]),(0,[z0,z1188,z1,z2,z3,z5]),(0,[z0,z9,z206,z1,z2,z7]),(0,[z0,z1189,z2,z3,z7,z5]),(0,[z0,z9,z1,z2,z7,z5])],[(0,[z0,z1,z2,z99,z203,z5]),(0,[z38,z142,z39,z3,z7,z5]),(0,[z1,z2,z714,z3,z7,z5]),(0,[z0,z1,z2,z10,z7,z164]),(0,[z0,z1,z1190,z3,z7,z5]),(0,[z0,z50,z90,z2,z3,z5]),(0,[z0,z18,z426,z1,z2,z5])],[(0,[z0,z1,z2,z1191,z7,z5]),(0,[z0,z1,z2,z3,z1192,z5]),(0,[z0,z1,z2,z149,z4,z5]),(0,[z1,z2,z3,z7,z715,z5]),(0,[z0,z1,z2,z3,z1193,z5])],[(0,[z0,z1194,z2,z3,z7,z5]),(0,[z647,z1,z2,z41,z7,z5])],[(0,[z0,z169,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z1195,z5]),(0,[z0,z856,z1,z3,z7,z93]),(0,[z1,z2,z3,z16,z192,z5]),(0,[z0,z263,z2,z63,z3,z7]),(0,[z0,z1,z2,z7,z800,z5])]]]

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
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 523).take 533) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1056).take 189) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1245)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [523, 533, 189] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 102).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 102).take 108).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 210).take 46).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [102, 108, 46] = true :=
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

end PEqualNP.Outside.L_meta_38795

theorem PEqualNP.Outside.L_meta_38795 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4272605184) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4272605184) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38795.solve